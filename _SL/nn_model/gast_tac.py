import json

import torch
import torch.nn as nn
from torch.nn import Conv1d, MaxPool1d, Linear, Dropout
import torch.nn.functional as F

from torch_geometric.nn import GCNConv, global_sort_pool
from torch_geometric.utils import remove_self_loops

from helpers import get_tactic_targets, get_tactics_true, get_args_true, get_tactics_pred, prep_asts

class GastTac(nn.Module):
    def __init__(self, opts):
        super(GastTac, self).__init__()
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
        self.classifier_1 = Linear(self.dense_dim, self.opts.embedding_dim)
        self.drop_out = Dropout(self.opts.dropout)
        self.classifier_2 = Linear(self.opts.embedding_dim, len(self.tactics))
        self.relu = nn.ReLU(inplace=True)
        self.tanh = nn.Tanh()
            
        self.criterion = nn.CrossEntropyLoss().to(self.opts.device)
        self.softmax = nn.Softmax(dim=-1)
        

    def forward(self, batch):
        asts = [goal['ast'] for goal in batch['goal']]
        x, edge_index, gnn_batch = prep_asts(self.opts, asts, len(asts))
        edge_index, _ = remove_self_loops(edge_index)
        edge_index.to(self.opts.device)
        
        x_1 = self.tanh(self.conv1(x, edge_index))
        x_2 = self.tanh(self.conv2(x_1, edge_index))
        x_3 = self.tanh(self.conv3(x_2, edge_index))
        x_4 = self.tanh(self.conv4(x_3, edge_index))
        x = torch.cat([x_1, x_2, x_3, x_4], dim=-1)
        x = global_sort_pool(x, gnn_batch, k=self.opts.sortk)
        x = x.view(x.size(0), 1, x.size(-1))
        x = self.relu(self.conv5(x))
        x = self.pool(x)
        x = self.relu(self.conv6(x))
        x = x.view(x.size(0), -1)
        out = self.relu(self.classifier_1(x))
        out = self.drop_out(out)
        logits = self.classifier_2(out)

        targets = get_tactic_targets(self.opts, self.tactics, batch)
        loss = self.criterion(logits, targets)
        trues = get_tactics_true(batch)
        probs = self.softmax(logits)
        preds = get_tactics_pred(self.tactics, probs)
        return preds, trues, loss

    def prove(self, goal, lc, gc):
        asts = [goal["ast"]]
        x, edge_index, gnn_batch = prep_asts(self.opts, asts, len(asts))
        edge_index, _ = remove_self_loops(edge_index)
        
        x_1 = self.tanh(self.conv1(x, edge_index))
        x_2 = self.tanh(self.conv2(x_1, edge_index))
        x_3 = self.tanh(self.conv3(x_2, edge_index))
        x_4 = self.tanh(self.conv4(x_3, edge_index))
        x = torch.cat([x_1, x_2, x_3, x_4], dim=-1)
        x = global_sort_pool(x, gnn_batch, k=self.opts.sortk)
        x = x.view(x.size(0), 1, x.size(-1))
        x = self.relu(self.conv5(x))
        x = self.pool(x)
        x = self.relu(self.conv6(x))
        x = x.view(x.size(0), -1)
        out = self.relu(self.classifier_1(x))
        logits = self.classifier_2(out)
        probs = self.softmax(logits)
        return probs[0]
