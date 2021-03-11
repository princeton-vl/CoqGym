import torch
import torch.nn as nn
import json
from .embedder import Embedder
from .predictor import Predictor

#all_acc = []
#batch_count = 0

class Prover(nn.Module):
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        with open('./tactic_groups.json', 'r') as f: self.tactic_groups = json.load(f)
        with open('./tactic_groups_reverse.json', 'r') as f: self.tactic_groups_reverse = json.load(f)
        with open('./nonterminals.json', 'r') as f: 
            self.nonterminals = json.load(f)
        self.predictor = Predictor(self.opts, self.tactic_groups)
        self.goal_embedder = Embedder(self.opts, self.nonterminals)
        self.lc_embedder = Embedder(self.opts, self.nonterminals)
        self.gc_embedder = Embedder(self.opts, self.nonterminals)

    def forward(self, batch):
        # compute goal embeddings
        goal_asts = batch['goal_ast']
        goal_embeddings = self.goal_embedder(goal_asts)

        # compute lc embeddings
        lc_sizes = [len(lc) for lc in batch['local_context']]
        lc_asts = self.get_context_asts(batch['local_context'])
        lc_embeddings = self.lc_embedder(lc_asts)
        lc_embeddings = self.prep_context_embeddings(lc_embeddings, lc_sizes)

        # compute gc embeddings
        gc_sizes = [len(lc) for lc in batch['env']]
        gc_asts = self.get_context_asts(batch['env'])
        gc_embeddings = self.gc_embedder(gc_asts)
        gc_embeddings = self.prep_context_embeddings(gc_embeddings, gc_sizes)

        # concatenate embeddings
        embeddings = torch.cat((goal_embeddings, lc_embeddings, gc_embeddings), 1)

        # predict tactic group
        preds = self.predictor(embeddings)

        # compute loss
        true_tactics = batch['tactic_str']
        true_groups = self.get_groups(true_tactics)
        loss = self.compute_loss(preds, true_groups, len(true_tactics))
        pred_groups = self.get_groups_preds(preds)
        return pred_groups, true_groups, loss

    def get_context_asts(self, c):
        asts = []
        for current_c in c:
            if not current_c:
                asts += [None]
            else:
                asts += [r['ast'] for r in current_c]
        return asts

    def prep_context_embeddings(self, embeddings, sizes):
        res = []
        j = 0
        for i, size in enumerate(sizes):
            context_embedding = embeddings[j:j+size].sum(0)
            res.append(
                context_embedding
            )
            j += size
        return torch.stack(res)

    def get_groups(self, tactics):
        res = []
        for tactic in tactics:
            all_actions = tactic.split(" ")
            if all_actions[0] in self.tactic_groups_reverse:
                res.append(self.tactic_groups_reverse[all_actions[0]])
            else:
                res.append("other")
        return res
    
    def get_groups_preds(self, preds):
        res = []
        for pred in preds:
            current_pred = list(self.tactic_groups.keys())[torch.argmax(pred)]
            res.append(current_pred)
        return res
    
    def compute_loss(self, groups_pred, groups_true, current_batchsize):
        targets = self.tactic_space_mapping(groups_true, current_batchsize)
        criterion = nn.CrossEntropyLoss()
        loss = criterion(groups_pred, targets)
        return loss

        """
        acc = self.acc(groups_pred, targets)
        global all_acc, batch_count
        all_acc.append(acc)
        batch_count += 1
        av_acc = (sum(all_acc))/batch_count

        pred_map = {}
        for pred in groups_pred:
            current_pred = list(self.tactic_groups.keys())[torch.argmax(pred)]
            pred_map[current_pred] = pred_map.get(current_pred, 0) + 1
        true_map = {}
        for target in targets:
            current_true = list(self.tactic_groups.keys())[target]
            true_map[current_true] = true_map.get(current_true, 0) + 1
        """

        """
        print("---")
        print(pred_map)
        print(true_map)
        print(f"Current acc: {acc}")
        print(f"Average acc: {av_acc}")
        print("---")
        
        true_prediction = self.tactic_space[torch.argmax(tactic_preds)]
        print("------")
        print(true_prediction)
        print(tactic_true)
        print("------")
        """
        # return loss

    def tactic_space_mapping(self, actions, current_batchsize):
        target = torch.empty(current_batchsize, dtype=torch.long)
        for i, action in enumerate(actions):
            index = list(self.tactic_groups.keys()).index("other")
            for group in self.tactic_groups.keys():
                if group == action:
                    index = list(self.tactic_groups.keys()).index(group)
            target[i] = index
        return target

    def acc(self, preds, targets):
        acc = 0
        for i, pred in enumerate(preds):
            pred_index = torch.argmax(pred)
            if (pred_index == targets[i]):
                acc += 1

        return acc/self.opts.batchsize

