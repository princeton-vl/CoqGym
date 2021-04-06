import os, sys, json
sys.path.append(os.path.abspath('../'))
from gallina import traverse_postorder

import torch
import torch.nn as nn
import torch.nn.functional as F
from helpers import get_tactic_targets, get_true_tactics, get_true_args, get_pred_tactics

class FFNArgModel(nn.Module):
    def __init__(self, opts):
        super(FFNArgModel, self).__init__()
        self.opts = opts
        with open(self.opts.args) as f: self.args = json.load(f)
        with open(self.opts.nonterminals) as f: self.nonterminals = json.load(f)
                
        self.input = nn.Linear(2*len(self.nonterminals), len(self.nonterminals))
        self.hidden = nn.Linear(len(self.nonterminals), len(self.nonterminals))

        self.output = nn.Linear(len(self.nonterminals), 1)
            
        self.activation = nn.Tanh()
        self.dropout = nn.Dropout(self.opts.dropout)
        self.sigmoid = nn.Sigmoid()
        class_weights = torch.tensor([1])
        self.bce_loss = nn.BCEWithLogitsLoss(pos_weight=class_weights).to(self.opts.device)
        
    def forward(self, batch):
        goal_asts = [goal["ast"] for goal in batch["goal"]]
        goal_encodings = self.ast_encodings(goal_asts)
        tactic_applications = [tactic["text"] for tactic in batch["tactic"]]
        
        encodings = []
        trues = []
        targets = []
        preds = []
        for i, goal_encoding in enumerate(goal_encodings):
            global_encodings, global_targets, global_pred = self.global_encodings(goal_encoding, tactic_applications[i], batch["env"][i])
            local_encodings, local_targets, local_pred = self.local_encodings(goal_encoding, tactic_applications[i], batch["local_context"][i])
            
            if len(global_encodings) == 0 or len(local_encodings) == 0:
                continue

            
            preds.extend(global_pred)
            preds.extend(local_pred)
            
            encodings.extend(global_encodings)
            encodings.extend(local_encodings)
            
            trues.extend([tactic_applications[i]]*(len(global_encodings)+len(local_encodings)))
                        
            targets.extend(global_targets)
            targets.extend(local_targets)
            
        encodings = torch.stack(encodings)
        targets = torch.stack(targets)
        
        x = self.input(encodings)
        x = self.activation(x)
        x = self.dropout(x)
        x = self.hidden(x)
        x = self.activation(x)
        x = self.dropout(x)
        logits = self.output(x)
        
        loss = self.bce_loss(logits, targets)
        probs = self.sigmoid(logits)
        
        num_correct = 0
        total_count = 0
        for i, prob in enumerate(probs):
            total_count += 1
            if prob <= 0.5:
                preds[i] = "NONE"
                if targets[i] == 0:
                    num_correct += 1
            else:
                if targets[i] == 1:
                    num_correct += 1
            
        return preds, trues, loss, num_correct, total_count
    

    def local_encodings(self, goal_encoding, tactic_application, lc):
        lc_asts = [c["ast"] for c in lc]
        lc_ids = [c["ident"] for c in lc]
        
        if len(lc_asts) == 0:
            return [], [], []
        
        lc_encodings = self.ast_encodings(lc_asts)
        encodings = []
        targets = []
        preds = []
        for j, lc_encoding in enumerate(lc_encodings):
            encodings.append(torch.cat([goal_encoding, lc_encoding], dim=0))
            
            lc_id = lc_ids[j]
            preds.append(lc_id)
            
            target = torch.zeros(1).to(self.opts.device)
            for element in tactic_application.split(" "):
                if element == lc_id and element not in self.args:
                    target = torch.ones(1).to(self.opts.device)
            
            targets.append(target)
            
        return encodings, targets, preds
            
                
    def global_encodings(self, goal_encoding, tactic_application, gc):
        gc_asts = [c["ast"] for c in gc]
        gc_ids = [c["qualid"] for c in gc]
        
        if len(gc_asts) == 0:
            return [], [], []
            
        gc_encodings = self.ast_encodings(gc_asts)
        encodings = []
        targets = []
        preds = []
        for j, gc_encoding in enumerate(gc_encodings):
            encodings.append(torch.cat([goal_encoding, gc_encoding], dim=0))
            
            gc_id = gc_ids[j]
            preds.append(gc_id)
            
            target = torch.zeros(1).to(self.opts.device)
            if "." in gc_id:
                pieces = gc_id.split(".")
                for piece in pieces:
                    if piece in tactic_application:
                        target = torch.ones(1).to(self.opts.device)
            else:
                if gc_id in tactic_application:
                    target = torch.ones(1).to(self.opts.device)
            targets.append(target)

        return encodings, targets, preds
                    
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
        