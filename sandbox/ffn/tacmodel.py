import os, sys, json
sys.path.append(os.path.abspath('../'))
from gallina import traverse_postorder

import torch
import torch.nn as nn
import torch.nn.functional as F
from helpers import get_tactic_targets, get_true_tactics, get_true_args, get_pred_tactics

class FFNTacModel(nn.Module):
    def __init__(self, opts):
        super(FFNTacModel, self).__init__()
        self.opts = opts
        
        self.nonterminals = json.load(open(self.opts.nonterminals))
        self.tactics = json.load(open(self.opts.tactics))
        
        self.input = nn.Linear(len(self.nonterminals), len(self.nonterminals))
        self.hidden = nn.Linear(len(self.nonterminals), len(self.nonterminals))
        self.output = nn.Linear(len(self.nonterminals), len(self.tactics))
            
        self.activation = nn.Tanh()
        self.dropout = nn.Dropout(self.opts.dropout)
        self.softmax = nn.Softmax(dim=1)
        self.cross_entropy = nn.CrossEntropyLoss().to(self.opts.device)
        
    def forward(self, batch):
        goal_asts = [goal["ast"] for goal in batch["goal"]]    
        goal_encodings = self.ast_encodings(goal_asts)
        
        x = self.input(goal_encodings)
        x = self.activation(x)
        x = self.dropout(x)
        x = self.hidden(x)
        x = self.activation(x)
        x = self.dropout(x)
        logits = self.output(x)
        targets = get_tactic_targets(self.opts, self.tactics, batch)
        loss = self.cross_entropy(logits, targets)
        trues = get_true_tactics(batch)
        probs = self.softmax(logits)
        preds = get_pred_tactics(self.tactics, probs)
        return preds, trues, loss

    def ast_encodings(self, asts):
        num_asts = len(asts)
        encodings = []
        for i, ast in enumerate(asts):
            if ast != None:
                encoding = self.ast_encode(ast)
                encodings.append(encoding)
        if not encodings:
            return []
        return torch.stack(encodings).to(self.opts.device)
    
        
    def ast_encode(self, ast):
        res = [0.0]*len(self.nonterminals)
        
        def callbck(node):
            index = self.nonterminals.index(node.data)
            res[index] += 1.0

        traverse_postorder(ast, callbck)
        return torch.tensor(res).to(self.opts.device)
    
        
    def prove(self, goal, local_context, global_context):
        goal_ast = goal['ast']
        goal_encodings = self.ast_encode(goal_ast)
        x = self.input(goal_encodings)
        x = self.activation(x)
        x = self.hidden(x)
        x = self.activation(x)
        logits = self.output(x)
        probs = F.softmax(logits, dim=0)
        return probs
        
        
        
        
        