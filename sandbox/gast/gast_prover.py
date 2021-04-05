import torch
import torch.nn as nn
from torch.nn import Sequential as Seq, Linear as Lin, ReLU
import torch.nn.functional as F
from helpers import ProofStepData, merge, traverse_postorder, get_node_count_ast
from .sage import SAGEEmbedder
from .sg import SGEmbedder
from .conv_and_dense import ConvAndDense
import json

class GASTProver(nn.Module):
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.embedder = opts.embedder
        with open(f'{opts.jsonpath}/tactic_groups.json', 'r') as f: 
            self.tactic_groups = json.load(f)
        with open(f'{opts.jsonpath}/tactic_groups_reverse.json', 'r') as f: 
            self.tactic_groups_reverse = json.load(f)
        with open(f'{opts.jsonpath}/nonterminals.json', 'r') as f: 
            self.nonterminals = json.load(f)
        
        if self.opts.embedding_info == "goal":
            self.embedding_dim_c = 1
        elif self.opts.embedding_info == "goal+lc":
            self.embedding_dim_c = 2
        elif self.opts.embedding_info == "goal+lc+gc":
            self.embedding_dim_c = 3
        
        # "mlp", "gcnconv", "sgconv", "sageconv", "gatconv", "transformerconv"
        if self.embedder == "mlp":
            self.goal_embedder = MLPEmbedder(self.opts, self.nonterminals)
        elif self.embedder == "gcnconv":
            self.goal_embedder = GCNEmbedder(self.opts, self.nonterminals)
        elif self.embedder == "sgconv":
            self.goal_embedder = SGEmbedder(self.opts, self.nonterminals)
            if self.opts.embedding_info == "goal+lc":
                self.lc_embedder = SGEmbedder(self.opts, self.nonterminals)
            elif self.opts.embedding_info == "goal+lc+gc":
                self.lc_embedder = SGEmbedder(self.opts, self.nonterminals)
                self.gc_embedder = SGEmbedder(self.opts, self.nonterminals)
        elif self.embedder == "sageconv":
            self.goal_embedder = SAGEEmbedder(self.opts, self.nonterminals)
            if self.opts.embedding_info == "goal+lc":
                self.lc_embedder = SAGEEmbedder(self.opts, self.nonterminals)
            elif self.opts.embedding_info == "goal+lc+gc":
                self.lc_embedder = SAGEEmbedder(self.opts, self.nonterminals)
                self.gc_embedder = SAGEEmbedder(self.opts, self.nonterminals)
        elif self.embedder == "gatconv":
            self.goal_embedder = GATEmbedder(self.opts, self.nonterminals)
        elif self.embedder == "transformerconv":
            self.goal_embedder = TransformerEmbedder(self.opts, self.nonterminals)
            
        if self.opts.pooling == "set2set":
            self.embedding_dim_c = self.embedding_dim_c*2
        elif self.opts.pooling == "sort":
            self.embedding_dim_c = self.embedding_dim_c*self.opts.sortk
        
        if self.opts.predictor == "linear":
            self.predictor = nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, len(self.tactic_groups))
            #self.lin.weight.data = self.lin.weight.data.clamp(min=0)
        elif self.opts.predictor == "mlp":
            self.predictor = Seq(
                nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, self.embedding_dim_c*self.opts.embedding_dim),
                nn.Tanh(),
                nn.Dropout(self.opts.dropout),
                nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, self.embedding_dim_c*self.opts.embedding_dim),
                nn.Tanh(),
                nn.Dropout(self.opts.dropout),
                nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, len(self.tactic_groups))
            )
        elif self.opts.predictor == "conv_and_dense":
            self.predictor = ConvAndDense(opts)
            
        self.dropout = nn.Dropout(self.opts.dropout)
        #self.activation = nn.Tanh()
        self.softmax = nn.Softmax(dim=1)

    def forward(self, batch):
        # compute goal embeddings
        goal_asts = [goal['ast'] for goal in batch['goal']]
        goal_embeddings = self.goal_embedder(goal_asts)
        
        if "lc" in self.opts.embedding_info:
            lc_sizes = [len(lc) for lc in batch['local_context']]
            lc_asts = self.get_context_asts(batch['local_context'])
            lc_embeddings = self.lc_embedder(lc_asts)
            lc_embeddings = self.prep_context_embeddings(lc_embeddings, lc_sizes)
            
        if "gc" in self.opts.embedding_info:
            gc_sizes = [len(lc) for lc in batch['env']]
            gc_asts = self.get_context_asts(batch['env'])
            gc_embeddings = self.gc_embedder(gc_asts)
            gc_embeddings = self.prep_context_embeddings(gc_embeddings, gc_sizes)
            
        if self.opts.embedding_info == "goal+lc":
            embeddings = torch.cat((goal_embeddings, lc_embeddings), 1)
        elif self.opts.embedding_info == "goal+lc+gc":
            embeddings = torch.cat((goal_embeddings, lc_embeddings, gc_embeddings), 1)
        elif self.opts.embedding_info == "goal":
            embeddings = goal_embeddings
        #print(embeddings)
        
        true_tactics = [tactic['text'] for tactic in batch['tactic']]
        true_groups = self.get_groups(true_tactics)
        
        
        logits = self.predictor(embeddings)
        logits = self.dropout(logits)
        #print(logits)
        
        loss = self.compute_loss(logits, true_groups, len(true_tactics))
        
        preds = self.softmax(logits)
        #print(preds)
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
        return torch.stack(res).to(self.opts.device)

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
        criterion = nn.CrossEntropyLoss().to(self.opts.device)
        loss = criterion(groups_pred, targets)
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
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        