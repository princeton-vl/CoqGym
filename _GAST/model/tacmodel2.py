import torch
import torch.nn as nn
from torch.nn import Sequential as Seq, Linear as Lin, ReLU
import torch.nn.functional as F
from helpers import get_tactic_targets, get_true_tactics, get_true_args, get_pred_tactics
from .dgcnn import Model
import json

class GASTTacModel2(nn.Module):
    def __init__(self, opts):
        super(GASTTacModel2, self).__init__()
        self.opts = opts
        self.nonterminals = json.load(open(self.opts.nonterminals))
        self.tactics = json.load(open(self.opts.tactics))
            
        self.criterion = nn.CrossEntropyLoss().to(self.opts.device)
        
        self.model = Model(self.opts, len(self.nonterminals), len(self.tactics), self.nonterminals)
        self.softmax = nn.Softmax(dim=-1)
        

    def forward(self, batch):
        # compute goal embeddings
        goal_asts = [goal['ast'] for goal in batch['goal']]
        
        logits = self.model(goal_asts)
        targets = get_tactic_targets(self.opts, self.tactics, batch)
        loss = self.criterion(logits, targets)
        trues = get_true_tactics(batch)
        probs = self.softmax(logits)
        preds = get_pred_tactics(self.tactics, probs)
        
        return preds, trues, loss
        