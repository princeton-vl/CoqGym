import json

import torch
import torch.nn as nn
from torch.nn import Conv1d, MaxPool1d, Linear, Dropout
import torch.nn.functional as F

from torch_geometric.nn import GCNConv, global_sort_pool
from torch_geometric.utils import remove_self_loops

from _SL.helpers import get_tactic_targets, get_tactics_true, get_args_true, get_tactics_pred, prep_asts, get_lc_targets, get_lc_pred

class GastLC(nn.Module):
    def __init__(self, opts):
        super(GastLC, self).__init__()
        self.opts = opts
        self.nonterminals = json.load(open(self.opts.nonterminals))
        self.tactics = json.load(open(self.opts.tactics))

        self.conv1 = GCNConv(len(self.nonterminals), self.opts.embedding_dim)
        self.conv2 = GCNConv(self.opts.embedding_dim, self.opts.embedding_dim)
        self.conv3 = GCNConv(self.opts.embedding_dim, self.opts.embedding_dim)
        self.conv4 = GCNConv(self.opts.embedding_dim, 1)
        self.conv5 = Conv1d(1, self.opts.embedding_dim//2, 3*self.opts.embedding_dim+1, 3*self.opts.embedding_dim+1)
        self.conv6 = Conv1d(self.opts.embedding_dim//2, self.opts.embedding_dim, 5, 1)
        self.pool = MaxPool1d(2, 2)
        dense_dim = int((self.opts.sortk - 2) / 2 + 1)
        self.dense_dim = (dense_dim - 5 + 1) * self.opts.embedding_dim
        self.classifier_1 = Linear(11*self.dense_dim, self.opts.embedding_dim)
        self.drop_out = Dropout(self.opts.dropout)
        self.classifier_2 = Linear(self.opts.embedding_dim, 10)
        self.relu = nn.ReLU(inplace=True)
        self.tanh = nn.Tanh()
            
        self.criterion = nn.CrossEntropyLoss().to(self.opts.device)
        self.softmax = nn.Softmax(dim=-1)
        

    def forward(self, batch):
        goal_asts_s = [g["ast"] for g in batch["goal"]]
        goal_embs = []
        for goal_asts in goal_asts_s:
            x_goal, edge_index_goal, gnn_batch = prep_asts(self.opts, [goal_asts], 1)
            edge_index_goal, _ = remove_self_loops(edge_index_goal)
            edge_index_goal.to(self.opts.device)
            goal_embeddings = self.embeddings(x_goal, edge_index_goal, gnn_batch)
            goal_embs.append(goal_embeddings)

        lc_asts_s = [[c["ast"] for c in lc] for lc in batch["local_context"]]
        lc_embs = []
        for lc_asts in lc_asts_s:
            x_lc, edge_index_lc, gnn_batch = prep_asts(self.opts, lc_asts, 10)
            edge_index_lc, _ = remove_self_loops(edge_index_lc)
            edge_index_lc.to(self.opts.device)

            lc_embeddings = self.embeddings(x_lc, edge_index_lc, gnn_batch)
            lc_embs.append(lc_embeddings)

        embs = []
        for i in range(len(goal_embs)):
            embeddings = torch.cat((goal_embs[i], lc_embs[i]))
            embeddings = torch.flatten(embeddings)
            embs.append(embeddings)
        embs = torch.stack(embs)

        out = self.relu(self.classifier_1(embs))
        out = self.drop_out(out)
        logits = self.classifier_2(out)

        targets, trues = get_lc_targets(self.opts, batch)

        loss = self.criterion(logits, targets)

        probs = self.softmax(logits)

        preds = get_lc_pred(self.opts, batch, probs)
        return preds, trues, loss

    def embeddings(self, x, edge_index, batch):
        x_1 = self.tanh(self.conv1(x, edge_index))
        x_2 = self.tanh(self.conv2(x_1, edge_index))
        x_3 = self.tanh(self.conv3(x_2, edge_index))
        x_4 = self.tanh(self.conv4(x_3, edge_index))
        x = torch.cat([x_1, x_2, x_3, x_4], dim=-1)
        x = global_sort_pool(x, batch, k=self.opts.sortk)
        x = x.view(x.size(0), 1, x.size(-1))
        x = self.relu(self.conv5(x))
        x = self.pool(x)
        x = self.relu(self.conv6(x))
        x = x.view(x.size(0), -1)
        return x

    def prove(self, goal, lc, gc):
        goal_asts = [goal["ast"]]
        lc_asts = [c["ast"] for c in lc]
        asts = goal_asts + lc_asts

        x, edge_index, batch = prep_asts(self.opts, asts, 11)
        edge_index, _ = remove_self_loops(edge_index)
            
        embeddings = self.embeddings(x, edge_index, batch)
        embeddings = torch.flatten(embeddings)

        out = self.relu(self.classifier_1(embeddings))
        
        logits = self.classifier_2(out)
        logits = logits.view(-1, len(logits))
        probs = self.softmax(logits)

        return probs[0]
