import torch
import torch.nn as nn
import json
from .term_embedder import TermEmbedder
from .tactic_predictor import TacticPredictor

all_acc = []
batch_count = 0

class Prover(nn.Module):
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        with open('./tactic_space.json', 'r') as f: self.tactic_space = json.load(f)[self.opts.tactic_space]
        with open('./nonterminals.json', 'r') as f: 
            self.nonterminals = json.load(f)
        self.tactic_predictor = TacticPredictor(self.opts, self.tactic_space)
        self.term_embedder = TermEmbedder(self.opts, self.nonterminals)
    

    def forward(self, batch):
        goal_asts = batch['goal_ast']
        goal_embeddings = self.term_embedder(goal_asts)

        lc_sizes = [len(lc) for lc in batch['local_context']]
        lc_asts = self.get_context_asts(batch['local_context'])
        lc_embeddings = self.term_embedder(lc_asts)
        lc_embeddings = self.prep_context_embeddings(lc_embeddings, lc_sizes)

        embeddings = torch.cat((goal_embeddings, lc_embeddings), 1)

        preds = self.tactic_predictor(embeddings)

        true_tactics = batch['tactic_str']
        loss = self.compute_loss(preds, true_tactics)

        return loss

    
    def compute_loss(self, tactic_preds, tactic_true):
        targets = self.tactic_space_mapping(tactic_true)
        criterion = nn.CrossEntropyLoss()
        loss = criterion(tactic_preds, targets)
        acc = self.acc(tactic_preds, targets)
        global all_acc, batch_count
        all_acc.append(acc)
        batch_count += 1
        av_acc = (sum(all_acc))/batch_count

        pred_map = {}
        for pred in tactic_preds:
            current_pred = self.tactic_space[torch.argmax(pred)]
            pred_map[current_pred] = pred_map.get(current_pred, 0) + 1
        true_map = {}
        for target in targets:
            current_true = self.tactic_space[target]
            true_map[current_true] = true_map.get(current_true, 0) + 1

        print("---")
        print(pred_map)
        print(true_map)
        print(f"Current acc: {acc}")
        print(f"Average acc: {av_acc}")
        print("---")
        """
        true_prediction = self.tactic_space[torch.argmax(tactic_preds)]
        print("------")
        print(true_prediction)
        print(tactic_true)
        print("------")
        """
        return loss
    

    def tactic_space_mapping(self, actions):
        target = torch.empty(self.opts.batchsize, dtype=torch.long)
        for i, action in enumerate(actions):
            index = self.tactic_space.index("OUT OF VOCAB")
            for tactic in self.tactic_space:
                if tactic in action:
                    index = self.tactic_space.index(tactic)
            target[i] = index
        return target

    def acc(self, preds, targets):
        acc = 0
        for i, pred in enumerate(preds):
            pred_index = torch.argmax(pred)
            if (pred_index == targets[i]):
                acc += 1

        return acc/self.opts.batchsize
    
    
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

