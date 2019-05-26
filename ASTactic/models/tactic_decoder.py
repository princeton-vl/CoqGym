import torch
import torch.nn as nn
import torch.nn.functional as F
import math
import random
import pdb
from copy import deepcopy
from tac_grammar import TerminalNode, NonterminalNode
from lark.lexer import Token


class AvgLoss:
    'Maintaining the average of a set of losses'

    def __init__(self, device):
        self.sum = torch.tensor(0., device=device)
        self.num = 0


    def add(self, v):
        self.sum += v
        self.num += 1

    def value(self):
        return self.sum / self.num


class ContextReader(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.linear1 = nn.Linear(opts.hidden_dim + opts.term_embedding_dim + 3, opts.hidden_dim)
        self.relu1 = nn.ReLU()
        self.linear2 = nn.Linear(opts.hidden_dim, 1)
        self.default_context = torch.zeros(self.opts.term_embedding_dim + 3, device=self.opts.device)


    def forward(self, states, embeddings):
        assert states.size(0) == len(embeddings) 
        context = []
        for state, embedding in zip(states, embeddings):
            if embedding.size(0) == 0:  # no premise
                context.append(self.default_context)
            else:
                input = torch.cat([state.unsqueeze(0).expand(embedding.size(0), -1), embedding], dim=1)
                weights = self.linear2(self.relu1(self.linear1(input)))
                weights = F.softmax(weights, dim=0)
                context.append(torch.matmul(embedding.t(), weights).squeeze())
        context = torch.stack(context)
        return context


class ContextRetriever(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.linear1 = nn.Linear(opts.hidden_dim + opts.term_embedding_dim + 3, opts.hidden_dim)
        self.relu1 = nn.ReLU()
        self.linear2 = nn.Linear(opts.hidden_dim, 1)


    def forward(self, state, embeddings):
        input = torch.cat([state.unsqueeze(0).expand(embeddings.size(0), -1), embeddings], dim=1)
        logits = self.linear2(self.relu1(self.linear1(input)))
        return logits.view(logits.size(0))


def clear_state(node):
    del node.state


class TacticDecoder(nn.Module):

    def __init__(self, grammar, opts):
        super().__init__()
        self.opts = opts
        self.grammar = grammar
        self.symbol_embeddings = nn.Embedding(len(self.grammar.symbols), opts.symbol_dim)
        self.production_rule_embeddings = nn.Embedding(len(self.grammar.production_rules), opts.embedding_dim)
        self.lex_rule_embeddings = nn.Embedding(len(self.grammar.terminal_symbols), opts.embedding_dim)
        self.default_action_embedding = torch.zeros(self.opts.embedding_dim, device=self.opts.device)
        self.default_state = torch.zeros(self.opts.hidden_dim, device=self.opts.device)
        self.controller = nn.GRUCell(2 * opts.embedding_dim + 2 * opts.term_embedding_dim + 6 + opts.hidden_dim + opts.symbol_dim, opts.hidden_dim)
        self.state_decoder = nn.Sequential(nn.Linear(opts.hidden_dim, opts.embedding_dim), nn.Tanh())
        self.context_reader = ContextReader(opts)
        self.context_retriever = ContextRetriever(opts)
        self.INT_classifier = nn.Sequential(nn.Linear(opts.hidden_dim, opts.hidden_dim // 2), 
                                            nn.ReLU(inplace=True),
                                            nn.Linear(opts.hidden_dim // 2, 4))

        self.hint_dbs = ['arith', 'zarith', 'algebra', 'real', 'sets', 'core', 'bool', 'datatypes', 'coc', 'set', 'zfc']
        self.HINT_DB_classifier = nn.Sequential(nn.Linear(opts.hidden_dim, opts.hidden_dim // 2),
                                                nn.ReLU(inplace=True),
                                                nn.Linear(opts.hidden_dim // 2, len(self.hint_dbs)))

    def action2embedding(self, action):
        if isinstance(action, tuple):  # a production rule
            idx = self.grammar.production_rules.index(action)
            return self.production_rule_embeddings(torch.LongTensor([idx]).to(self.opts.device)).squeeze()
        else:  # a token
            idx = self.grammar.terminal_symbols.index(action)
            return self.lex_rule_embeddings(torch.LongTensor([idx]).to(self.opts.device)).squeeze()


    def gather_frontier_info(self, frontiers):
        indice = []  # indice for incomplete ASTs
        s_tm1 = []
        a_tm1 = []
        p_t = []
        symbols = []

        for i, stack in enumerate(frontiers):
            if stack == []:
                continue
            indice.append(i)
            node = stack[-1]  # the next node to expand
            if node.pred is None:  # root
                assert node.parent is None
                s_tm1.append(self.default_state)
                a_tm1.append(self.default_action_embedding)
                p_t.append(torch.cat([self.default_state, self.default_action_embedding]))
            else:
                s_tm1.append(node.pred.state)
                a_tm1.append(self.action2embedding(node.pred.action))
                p_t.append(torch.cat([node.parent.state, self.action2embedding(node.parent.action)]))
            symbols.append(node.symbol)

        if indice == []:  # all trees are complete
            return [], None, None, None, None

        symbol_indice = torch.LongTensor([self.grammar.symbols.index(s) for s in symbols])
        n_t = self.symbol_embeddings(symbol_indice.to(self.opts.device))
        s_tm1 = torch.stack(s_tm1)
        a_tm1 = torch.stack(a_tm1)
        p_t = torch.stack(p_t)        
        return indice, s_tm1, a_tm1, p_t, n_t


    def initialize_trees(self, batchsize):
        asts = [NonterminalNode(self.grammar.start_symbol, parent=None) for i in range(batchsize)]  # partial results
        frontiers = [[asts[i]] for i in range(batchsize)]  # the stacks for DFS, whose top are the next nodes
        return asts, frontiers


    def expand_node_set_pred(self, node, rule, stack):
        node.expand(rule)

        # updat the links to the predecessor
        for c in node.children[::-1]:
            if isinstance(c, Token):
                continue
            if stack != []:
                stack[-1].pred = c
            stack.append(c)

        if stack != []:
            stack[-1].pred = node


    def expand_nonterminal(self, node, expansion_step, nonterminal_expansion_step, actions_gt, teacher_forcing, stack):
        # selcet a production rule and compute the loss
        applicable_rules = self.grammar.get_applicable_rules(node.symbol)

        if teacher_forcing:
            logits = torch.matmul(self.production_rule_embeddings.weight[applicable_rules], self.state_decoder(node.state))
            action_idx = actions_gt[expansion_step]
            rule = self.grammar.production_rules[action_idx]  # expand the tree using the ground truth action 
            action_gt_onehot = torch.LongTensor([applicable_rules.index(action_idx)]).to(self.opts.device)
            loss = F.cross_entropy(logits.unsqueeze(0), action_gt_onehot)

        else:
            logits = torch.matmul(self.production_rule_embeddings.weight, self.state_decoder(node.state))
            rule_idx = applicable_rules[logits[applicable_rules].argmax().item()]
            rule = self.grammar.production_rules[rule_idx]
            if nonterminal_expansion_step < len(actions_gt):
                action_idx = actions_gt[nonterminal_expansion_step]
                action_gt_onehot = torch.LongTensor([action_idx]).to(self.opts.device)
                loss = F.cross_entropy(logits.unsqueeze(0), action_gt_onehot)
            else:
                loss = 0.
            
            if expansion_step > self.opts.size_limit:  # end the generation process asap
                rule_idx = applicable_rules[0]
                rule = self.grammar.production_rules[rule_idx]

        self.expand_node_set_pred(node, rule, stack)

        return loss


    def expand_terminal(self, node, expansion_step, environment, local_context, goal, actions_gt, teacher_forcing):
        loss = 0.        
        if teacher_forcing:
            token_gt = actions_gt[expansion_step]

        if node.symbol in ['QUALID', 'LOCAL_IDENT']:
            if node.symbol == 'QUALID':
                candidates = environment['idents'] + local_context['idents']
            else:
                candidates = local_context['idents']
            if candidates == []:
                token = random.choice(['H'] + goal['quantified_idents'])
            else:
                if node.symbol == 'QUALID':
                    candidate_embeddings = torch.cat([environment['embeddings'], local_context['embeddings']])
                else:
                    candidate_embeddings = local_context['embeddings']
                context_scores = self.context_retriever(node.state, candidate_embeddings)
                if teacher_forcing:
                    target = torch.zeros_like(context_scores)
                    if token_gt in candidates:
                        target[candidates.index(token_gt)] = 1.0
                    loss = F.binary_cross_entropy_with_logits(context_scores, target)
                else:
                    token = candidates[context_scores.argmax()]

        elif node.symbol in 'INT':
            cls = self.INT_classifier(node.state)
            if teacher_forcing:
                cls_gt = torch.LongTensor([int(token_gt) - 1]).to(self.opts.device)
                loss = F.cross_entropy(cls.unsqueeze(0), cls_gt)
            else:
                token = str(cls.argmax().item() + 1)

        elif node.symbol == 'HINT_DB':
            cls = self.HINT_DB_classifier(node.state)
            if teacher_forcing:
                cls_gt = torch.LongTensor([self.hint_dbs.index(token_gt)]).to(self.opts.device)
                loss = F.cross_entropy(cls.unsqueeze(0), cls_gt)
            else:
                token = self.hint_dbs[cls.argmax().item()]

        elif node.symbol == 'QUANTIFIED_IDENT':
            if goal['quantified_idents'] == []:
                candidates = ['x']
            else:
                candidates = goal['quantified_idents']
            token = random.choice(candidates)

        # generadddte a token with the lex rule
        node.expand(token_gt if teacher_forcing else token)

        return loss

    
    def expand_partial_tree(self, node, expansion_step, nonterminal_expansion_step, environment, local_context, goal, actions_gt, 
                            teacher_forcing, stack):
        assert node.state is not None
        if isinstance(node, NonterminalNode):
            return self.expand_nonterminal(node, expansion_step, nonterminal_expansion_step, actions_gt, teacher_forcing, stack)
        else:
            return self.expand_terminal(node, expansion_step, environment, local_context, goal, actions_gt, teacher_forcing)


    def forward(self, environment, local_context, goal, actions, teacher_forcing):
        if not teacher_forcing:
            # when train without teacher forcing, only consider the expansion of non-terminal nodes
            actions = [[a for a in act if isinstance(a, int)] for act in actions] 

        loss = AvgLoss(self.opts.device)

        # initialize the trees
        batchsize = goal['embeddings'].size(0)
        asts, frontiers = self.initialize_trees(batchsize)

        # expand the trees in a depth-first order
        expansion_step = 0
        nonterminal_expansion_step = [0 for i in range(batchsize)]
        while True:
            # in each iteration, compute the state of the frontier nodes and expand them
            # collect inputs from all partial trees: s_{t-1}, a_{t-1}, p_t, n_t
            indice, s_tm1, a_tm1, p_t, n_t = self.gather_frontier_info(frontiers)
            if indice == []:  # all trees are complete
                break 

            r = [torch.cat([environment[i]['embeddings'], local_context[i]['embeddings']], dim=0) for i in indice]
            u_t = self.context_reader(s_tm1, r)

            states = self.controller(torch.cat([a_tm1, goal['embeddings'][indice], u_t, p_t, n_t], dim=1), s_tm1)

            # store states and expand nodes
            for j, idx in enumerate(indice):
                stack = frontiers[idx]
                node = stack.pop()
                node.state = states[j]
                g = {k: v[idx] for k, v in goal.items()}
                loss.add(self.expand_partial_tree(node, expansion_step, nonterminal_expansion_step[idx], 
                                                  environment[idx], local_context[idx], g, actions[idx], teacher_forcing, stack))
                if isinstance(node, NonterminalNode):
                    nonterminal_expansion_step[idx] += 1

            expansion_step += 1

        for ast in asts:
            ast.traverse_pre(clear_state)

        return asts, loss.value()


    def duplicate(self, ast, stack):
        old2new = {}
        def recursive_duplicate(node, parent=None):
            if isinstance(node, Token):
                new_node = deepcopy(node)
                old2new[node] = new_node
                return new_node
            elif isinstance(node, TerminalNode):
                new_node = TerminalNode(node.symbol, parent)
                new_node.token = node.token
            else:
                assert isinstance(node, NonterminalNode)
                new_node = NonterminalNode(node.symbol, parent)

            old2new[node] = new_node
            new_node.action = node.action
            if node.pred is None:
                new_node.pred = None
            else:
                new_node.pred = old2new[node.pred]
            new_node.state = node.state
            if isinstance(node, NonterminalNode):
                for c in node.children:
                    new_node.children.append(recursive_duplicate(c, new_node))
            return new_node

        new_ast = recursive_duplicate(ast)
        new_stack = [old2new[node] for node in stack] 
        return new_ast, new_stack


    def beam_search(self, environment, local_context, goal):
        # initialize the trees in the beam
        assert goal['embeddings'].size(0) == 1  # only support batchsize == 1
        beam, frontiers = self.initialize_trees(1)
        log_likelihood = [0.]  # the (unnormalized) objective function maximized by the beam search
        complete_trees = []  # the complete ASTs generated during the beam search

        expansion_step = 0
        while True:
            # collect inputs from all partial trees
            indice, s_tm1, a_tm1, p_t, n_t = self.gather_frontier_info(frontiers)
            # check if there are complete trees 
            for i in range(len(beam)):
                if i not in indice:
                    normalized_log_likelihood = log_likelihood[i] / (expansion_step ** self.opts.lens_norm)  # length normalization
                    beam[i].traverse_pre(clear_state) 
                    complete_trees.append((beam[i], normalized_log_likelihood))
            if indice == []:  # all trees are complete, terminate the beam search
                break

            r = [torch.cat([environment['embeddings'], local_context['embeddings']], dim=0) for i in indice]
            u_t = self.context_reader(s_tm1, r)

            states = self.controller(torch.cat([a_tm1, goal['embeddings'].expand(len(indice), -1), u_t, p_t, n_t], dim=1), s_tm1)

            # compute the log likelihood and pick the top candidates
            beam_candidates = []
            for j, idx in enumerate(indice):
                stack = frontiers[idx]
                node = stack[-1]
                node.state = states[j]

                if isinstance(node, NonterminalNode):
                    applicable_rules = self.grammar.get_applicable_rules(node.symbol)
                    if expansion_step > self.opts.size_limit:  # end the generation process asap
                        beam_candidates.append((idx, log_likelihood[i], applicable_rules[0]))
                    else:
                        logits = torch.matmul(self.production_rule_embeddings.weight[applicable_rules], self.state_decoder(node.state))
                        log_cond_prob = logits - logits.logsumexp(dim=0)
                        for n, cand in enumerate(applicable_rules):
                            beam_candidates.append((idx, log_likelihood[idx] + log_cond_prob[n].item(), cand))

                elif node.symbol in ['QUALID', 'LOCAL_IDENT']:
                    if node.symbol == 'QUALID':
                        candidates = environment['idents'] + local_context['idents']
                    else:
                        candidates = local_context['idents']
                    if candidates == []:
                        candidates = ['H'] + goal['quantified_idents']
                        log_cond_prob = - math.log(len(candidates))
                        for cand in candidates:
                            beam_candidates.append((idx, log_likelihood[idx] + log_cond_prob, cand))
                    else:
                        if node.symbol == 'QUALID':
                            candidate_embeddings = torch.cat([environment['embeddings'], local_context['embeddings']])
                        else:
                            candidate_embeddings = local_context['embeddings']
                        context_scores = self.context_retriever(node.state, candidate_embeddings)
                        log_cond_prob = context_scores - context_scores.logsumexp(dim=0)
                        for n, cand in enumerate(candidates):
                            beam_candidates.append((idx, log_likelihood[idx] + log_cond_prob[n].item(), cand))
                       
                elif node.symbol == 'INT':
                    cls = self.INT_classifier(node.state)
                    log_cond_prob = cls - cls.logsumexp(dim=0)
                    for n in range(cls.size(0)):
                        beam_candidates.append((idx, log_likelihood[idx] + log_cond_prob[n].item(), str(n + 1)))

                elif node.symbol == 'HINT_DB':
                    cls = self.HINT_DB_classifier(node.state)
                    log_cond_prob = cls - cls.logsumexp(dim=0)
                    for n in range(cls.size(0)):
                        beam_candidates.append((idx, log_likelihood[idx] + log_cond_prob[n].item(), self.hint_dbs[n]))
              
                elif node.symbol == 'QUANTIFIED_IDENT':
                    if len(goal['quantified_idents']) > 0:
                        candidates = list(goal['quantified_idents'])
                    else:
                        candidates = ['x']
                    log_cond_prob = - math.log(len(candidates))
                    for cand in candidates:
                        beam_candidates.append((idx, log_likelihood[idx] + log_cond_prob, cand))

            # expand the nodes and update the beam
            beam_candidates = sorted(beam_candidates, key=lambda x: x[1], reverse=True)[:self.opts.beam_width]
            new_beam = []
            new_frontiers = []
            new_log_likelihood = []
            for idx, log_cond_prob, action in beam_candidates:
                ast, stack = self.duplicate(beam[idx], frontiers[idx])
                node = stack.pop()
                if isinstance(action, int):  # expand a nonterimial node
                    rule = self.grammar.production_rules[action]
                    self.expand_node_set_pred(node, rule, stack)
                else:  # expand a terminal node
                    node.expand(action)
                new_beam.append(ast)
                new_frontiers.append(stack)
                new_log_likelihood.append(log_likelihood[idx] + log_cond_prob)
            beam = new_beam
            frontiers = new_frontiers
            log_likelihood = new_log_likelihood
            expansion_step += 1

        complete_trees = sorted(complete_trees, key=lambda x: x[1], reverse=True)  # pick the top ASTs
        return [t[0] for t in complete_trees[:self.opts.num_tactic_candidates]]

