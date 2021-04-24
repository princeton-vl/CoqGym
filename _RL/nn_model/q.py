import json
from datetime import datetime

import torch
import torch.nn as nn
from torch.nn import Conv1d, MaxPool1d, Linear, Dropout
from torch_geometric.nn import GCNConv, global_sort_pool
from torch_geometric.utils import remove_self_loops

from gallina import traverse_postorder
import helpers

class Q(nn.Module):
    def __init__(self, opts):
        super(Q, self).__init__()
        self.opts = opts
        with open(opts.nonterminals) as f: self.nonterminals = json.load(f)
        self.action_space = self.opts.action_space

        ''' embedder '''
        self.conv1 = GCNConv(len(self.nonterminals), self.opts.embedding_dim)
        self.conv2 = GCNConv(self.opts.embedding_dim, self.opts.embedding_dim)
        self.conv3 = GCNConv(self.opts.embedding_dim, self.opts.embedding_dim)
        self.conv4 = GCNConv(self.opts.embedding_dim, 1)

        ''' extract features using convolutions after sort pooling '''
        self.conv5 = Conv1d(1, self.opts.embedding_dim//2, 3*self.opts.embedding_dim+1, 3*self.opts.embedding_dim+1)
        self.conv6 = Conv1d(self.opts.embedding_dim//2, self.opts.embedding_dim, 5, 1)
        self.pool = MaxPool1d(2, 2)

        ''' prediction network '''
        dense_dim = int((self.opts.sortk - 2) / 2 + 1)
        self.dense_dim = (dense_dim - 5 + 1) * self.opts.embedding_dim
        self.classifier_1 = Linear(self.dense_dim*31, self.opts.embedding_dim*3)
        self.classifier_2 = Linear(self.opts.embedding_dim*3, 35 + 20*6 + 10*8)

        ''' dropout and activation'''
        self.dropout = nn.Dropout(self.opts.dropout)
        self.relu = nn.ReLU(inplace=True)
        self.tanh = nn.Tanh()

    
    def forward(self, state):
        goal, lc, gc = state[0], state[1], state[2]
        goal_ast, lc_asts, gc_asts = goal['ast'], [c['ast'] for c in lc], [c['ast'] for c in gc]
        asts = [goal_ast] + lc_asts + gc_asts

        embedding = []
        for ast in asts:
            if ast.data == None:
                empty_x = torch.zeros(1, self.dense_dim)
                embedding.append(empty_x)
                continue

            ''' encode '''
            x, edge_index, batch = helpers.prep_ast(self.opts, ast)

            ''' embedd '''
            x_1 = self.tanh(self.conv1(x, edge_index))
            #print(x_1)
            x_2 = self.tanh(self.conv2(x_1, edge_index))
            x_3 = self.tanh(self.conv3(x_2, edge_index))
            x_4 = self.tanh(self.conv4(x_3, edge_index))
        
            ''' readout '''
            x = torch.cat([x_1, x_2, x_3, x_4], dim=-1)
            #print(x)
            x = global_sort_pool(x=x, batch=batch, k=self.opts.sortk)
            x = x.view(x.size(0), 1, x.size(-1))
            #print(x)
            ''' conv and pool '''
            x = self.relu(self.conv5(x))
            x = self.pool(x)
            x = self.relu(self.conv6(x))
            x = x.view(x.size(0), -1)
            #print(x)
            embedding.append(x)

        ''' concatenate '''
        embedding = torch.stack(embedding)
        embedding = embedding.flatten()

        ''' prediction '''
        out = self.tanh(self.classifier_1(embedding))
        out = self.dropout(out)
        logits = self.tanh(self.classifier_2(out))
        #print(logits)
        return logits
