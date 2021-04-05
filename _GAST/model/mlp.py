import torch
import torch.nn as nn
import torch_geometric.nn as gnn
from torch_geometric.data import Data, Batch
from torch_geometric.nn import global_mean_pool, global_max_pool, global_add_pool, Set2Set
from torch_geometric.nn.pool import TopKPooling
from torch_geometric.nn import GCNConv, SGConv, TransformerConv, SAGEConv, GATConv
from torch_geometric.nn.norm import GraphSizeNorm
from helpers import traverse_postorder, get_node_count_ast

class MLPEmbedder(gnn.MessagePassing):
    def __init__(self, opts, nonterminals):
        super(MLPEmbedder, self).__init__()
        self.opts = opts
        self.nonterminals = nonterminals
        self.hops = self.opts.hops
        self.embedding_dim = self.opts.embedding_dim
        
        self.mlp_v = nn.Sequential(
            nn.Linear(len(self.nonterminals), self.embedding_dim),
            nn.ReLU(),
            nn.Dropout(p=self.opts.dropout),
            nn.Linear(self.embedding_dim, self.embedding_dim),
            nn.ReLU(),
            nn.Dropout(p=self.opts.dropout),
            nn.Linear(self.embedding_dim, self.embedding_dim)
        )
        self.mlp_message = nn.Sequential(
            nn.Linear(2*self.embedding_dim, self.embedding_dim),
            nn.ReLU(),
            nn.Dropout(p=self.opts.dropout),
            nn.Linear(self.embedding_dim, self.embedding_dim),
            nn.ReLU(),
            nn.Dropout(p=self.opts.dropout),
            nn.Linear(self.embedding_dim, self.embedding_dim)
        )
        self.dropout = nn.Dropout(p=self.opts.dropout)

    def message(self, x_i, x_j):
        tmp = torch.cat([x_i, x_j], dim=1)
        return self.mlp_message(tmp)

    def forward(self, asts):
        embeddings = []
        graph_list = []
        for i, ast in enumerate(asts):
            if ast != None:
                edge_index = self.create_edge_index(ast)
                x = self.one_hot_encode(ast)
                data = Data(x=x, edge_index=edge_index).to(self.opts.device)
                graph_list.append(data)

        if graph_list:
            batch = Batch().from_data_list(graph_list)

            x = batch.x
            edge_index = batch.edge_index
            # inital embeddings
            x = self.mlp_v(x)

            # message passing
            try:
                for i in range(self.hops):
                    x = self.propagate(x=x, edge_index=edge_index)
                    x = x.relu()
                    x = self.dropout(x)
            except:
                all_empty = []
                for i, ast in enumerate(asts):
                    all_empty.append(torch.zeros(self.embedding_dim).to(self.opts.device))
                return torch.stack(all_empty)


            x = global_mean_pool(x, batch.batch)
            return x

        all_empty = []
        for i, ast in enumerate(asts):
            all_empty.append(torch.zeros(self.embedding_dim).to(self.opts.device))

        return torch.stack(all_empty)


    def create_edge_index(self, ast):
        index_map = {}
        counter = [0]
        def index_callbck(node):
            index_map[node.meta] = counter[-1]
            counter.append(counter[-1]+1)
            
        traverse_postorder(ast, index_callbck)
        edge_index = []
        def callbck(node):
            for child in node.children:
                parent_child = [index_map[node.meta], index_map[child.meta]]
                child_parent = [index_map[child.meta], index_map[node.meta]]
                edge_index.append(parent_child)
                edge_index.append(child_parent)
        
        traverse_postorder(ast, callbck)
        return torch.tensor(edge_index, dtype=torch.long).t().contiguous()

    def create_x(self, ast):
        x = []
        def callbck(node):
            x.append([self.nonterminals.index(node.data)])
        traverse_postorder(ast, callbck)
        return torch.tensor(x, dtype=torch.float)

    def one_hot_encode(self, ast):
        target = []
        def callbck(node):
            temp = [0.0]*len(self.nonterminals)
            index = self.nonterminals.index(node.data)
            temp[index] = 1.0
            target.append(temp)
        traverse_postorder(ast, callbck)
        return torch.tensor(target)
