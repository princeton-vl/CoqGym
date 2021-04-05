import torch
import torch.nn as nn
from torch.nn import Sequential as Seq, Linear as Lin, ReLU
import torch.nn.functional as F
from helpers import ProofStepData, merge, traverse_postorder, get_node_count_ast
import json

class ConvAndDense(nn.Module):
    def __init__(self, opts):
        super(ConvAndDense, self).__init__()
        self.opts = opts
        with open(f'{opts.jsonpath}/tactic_groups.json', 'r') as f: 
            self.tactic_groups = json.load(f)
        with open(f'{opts.jsonpath}/tactic_groups_reverse.json', 'r') as f: 
            self.tactic_groups_reverse = json.load(f)
        with open(f'{opts.jsonpath}/nonterminals.json', 'r') as f: 
            self.nonterminals = json.load(f)
            
        self.conv1d_params1 = nn.Conv1d(1, 16, self.opts.embedding_dim, self.opts.embedding_dim)
        
        self.maxpool1d = nn.MaxPool1d(2, 2)
        
        self.conv1d_params2 = nn.Conv1d(16, 32, 5, 1)
        
        self.activation = nn.ReLU()
        
        dense_dim = int((self.opts.sortk - 2) / 2 + 1)
        self.dense_dim = (dense_dim - 5 + 1) * 32
        
        self.dense = nn.Linear(self.dense_dim, self.dense_dim/2)
        self.out = nn.Linear(self.dense_dim, len(self.tactic_groups))
            
        
        
    def forward(self, embeddings):
        to_conv1d = embeddings.view((-1, 1, self.opts.sortk * self.opts.embedding_dim))
        conv1d_res = self.conv1d_params1(to_conv1d)
        conv1d_res = self.activation(conv1d_res)
        conv1d_res = self.maxpool1d(conv1d_res)
        conv1d_res = self.conv1d_params2(conv1d_res)
        conv1d_res = self.activation(conv1d_res)
        
        
        to_dense = conv1d_res.view(len(embeddings), -1)
        
        out_1 = self.dense(to_dense)
        out_1 = self.activation(out_1)
        out_2 = self.out(out_1)
        
        return out_2
    