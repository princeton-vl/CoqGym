import json

import torch
import torch.nn as nn
from torch.nn import Sequential as Seq, Linear as Lin, ReLU
import torch.nn.functional as F

from gallina import traverse_postorder
from helpers import get_tactic_targets, get_true_tactics, get_true_args, get_pred_tactics

from .sage import SAGEEmbedder
from .sg import SGEmbedder
from .conv_and_dense import ConvAndDense


class GASTTacModel(nn.Module):
    def __init__(self, opts):
        super(GASTTacModel, self).__init__()
        self.opts = opts
        self.embedder = opts.embedder
        self.nonterminals = json.load(open(self.opts.nonterminals))
        self.tactics = json.load(open(self.opts.tactics))
        
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
            self.predictor = nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, len(self.tactics))
            #self.lin.weight.data = self.lin.weight.data.clamp(min=0)
        elif self.opts.predictor == "mlp":
            self.predictor = Seq(
                nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, self.embedding_dim_c*self.opts.embedding_dim),
                nn.Tanh(),
                nn.Dropout(self.opts.dropout),
                nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, self.embedding_dim_c*self.opts.embedding_dim),
                nn.Tanh(),
                nn.Dropout(self.opts.dropout),
                nn.Linear(self.embedding_dim_c*self.opts.embedding_dim, len(self.tactics))
            )
        elif self.opts.predictor == "conv_and_dense":
            self.predictor = ConvAndDense(opts)
            
        self.dropout = nn.Dropout(self.opts.dropout)
        #self.activation = nn.Tanh()
        self.softmax = nn.Softmax(dim=1)
        self.cross_entropy = nn.CrossEntropyLoss().to(self.opts.device)

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
        
        logits = self.predictor(embeddings)
        logits = self.dropout(logits)
        
        targets = get_tactic_targets(self.opts, self.tactics, batch)
        
        loss = self.cross_entropy(logits, targets)
        trues = get_true_tactics(batch)
        probs = self.softmax(logits)
        preds = get_pred_tactics(self.tactics, probs)
        
        return preds, trues, loss

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

    def prove(self, goal, local_context, global_context):
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
             
        logits = self.predictor(embeddings)
        probs = F.softmax(logits, dim=0)
        return probs
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        