import json, torch
import torch.nn as nn
from .bert import BERTModel

class TransProver(nn.Module):
    def __init__(self, opts):
        super(TransProver, self).__init__()
        self.opts = opts
        with open(f'{opts.jsonpath}/tactic_groups.json', 'r') as f:
            self.tactic_groups = json.load(f)
        with open(f'{opts.jsonpath}/tactic_groups_reverse.json', 'r') as f: 
            self.tactic_groups_reverse = json.load(f)
        
  
        if self.opts.architecture == "bert":
            self.model = BERTModel(self.opts)

        self.softmax = nn.Softmax(dim=1)
        
    def forward(self, batch): 
        if self.opts.sexpression:
            goal_texts = [goal["sexpression"] for goal in batch["goal"]]
        else:
            goal_texts = [goal['text'] for goal in batch['goal']]
        
        for i, txt in enumerate(goal_texts):
            if txt == None:
                goal_texts[i] = "None"
                
        true_tactics = [tactic['text'] for tactic in batch['tactic']]
        groups_true = self.get_groups(true_tactics)
        labels = self.tactic_space_mapping(groups_true, len(goal_texts))
                
        
        logits, loss = self.model(goal_texts, labels)
    
        preds = self.softmax(logits)
        #print(preds)
        return self.get_groups_preds(preds), groups_true, loss

    def get_groups(self, tactics):
        res = []
        for tactic in tactics:
            all_actions = tactic.split(" ")
            if all_actions[0] in self.tactic_groups_reverse:
                res.append(self.tactic_groups_reverse[all_actions[0]])
            else:
                res.append("goal break up/other")
        return res

    def tactic_space_mapping(self, actions, current_batchsize):
        target = torch.empty(current_batchsize, dtype=torch.long).to(self.opts.device)
        for i, action in enumerate(actions):
            index = list(self.tactic_groups.keys()).index("goal break up/other")
            for group in self.tactic_groups.keys():
                if group == action:
                    index = list(self.tactic_groups.keys()).index(group)
            target[i] = index
        return target

    def get_groups_preds(self, preds):
        res = []
        for pred in preds:
            current_pred = list(self.tactic_groups.keys())[torch.argmax(pred)]
            res.append(current_pred)
        return res