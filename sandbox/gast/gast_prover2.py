import torch
import torch.nn as nn
from torch.nn import Sequential as Seq, Linear as Lin, ReLU
import torch.nn.functional as F
from helpers import ProofStepData, merge, traverse_postorder, get_node_count_ast
from .dgcnn import Model
import json

class GASTProver2(nn.Module):
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        with open(f'{opts.jsonpath}/tactic_groups.json', 'r') as f: 
            self.tactic_groups = json.load(f)
        with open(f'{opts.jsonpath}/tactic_groups_reverse.json', 'r') as f: 
            self.tactic_groups_reverse = json.load(f)
        with open(f'{opts.jsonpath}/nonterminals.json', 'r') as f: 
            self.nonterminals = json.load(f)
            
        self.criterion = nn.NLLLoss()
        
        self.model = Model(self.opts, len(self.nonterminals), len(self.tactic_groups), self.nonterminals)
        

    def forward(self, batch):
        # compute goal embeddings
        goal_asts = [goal['ast'] for goal in batch['goal']]
        
        true_tactics = [tactic['text'] for tactic in batch['tactic']]
        true_groups = self.get_groups(true_tactics)
        
        
        preds = self.model(goal_asts)
        loss = self.compute_loss(preds, true_groups, len(true_tactics))
        
        pred_groups = self.get_groups_preds(preds)
        return pred_groups, true_groups, loss


    def get_groups(self, tactics):
        res = []
        for tactic in tactics:
            all_actions = tactic.split(" ")
            if all_actions[0] in self.tactic_groups_reverse:
                res.append(self.tactic_groups_reverse[all_actions[0]])
            else:
                res.append("goal break up/other")
        return res
    
    def get_groups_preds(self, preds):
        res = []
        for pred in preds:
            current_pred = list(self.tactic_groups.keys())[torch.argmax(pred)]
            res.append(current_pred)
        return res
    
    def compute_loss(self, groups_pred, groups_true, current_batchsize):
        targets = self.tactic_space_mapping(groups_true, current_batchsize)
        loss = self.criterion(groups_pred, targets)
        return loss

    def tactic_space_mapping(self, actions, current_batchsize):
        target = torch.empty(current_batchsize, dtype=torch.long).to(self.opts.device)
        for i, action in enumerate(actions):
            index = list(self.tactic_groups.keys()).index("goal break up/other")
            for group in self.tactic_groups.keys():
                if group == action:
                    index = list(self.tactic_groups.keys()).index(group)
            target[i] = index
        return target
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        