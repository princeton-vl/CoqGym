import torch
import torch.nn as nn
import torch_geometric.nn as gnn
from torch_geometric.data import Data, Batch
from torch_geometric.nn import global_mean_pool, global_max_pool, global_add_pool, Set2Set, global_sort_pool
from torch_geometric.nn.pool import TopKPooling
from torch_geometric.nn import GCNConv, SGConv, TransformerConv, SAGEConv, GATConv
from torch_geometric.nn.norm import GraphSizeNorm
from helpers import traverse_postorder, get_node_count_ast

# SAGEConv
class SAGEEmbedder(torch.nn.Module):
    def __init__(self, opts, nonterminals):
        super(SAGEEmbedder, self).__init__()
        self.opts = opts
        self.nonterminals = nonterminals
        
        if self.opts.num_message_layers == 1:
            self.conv = SAGEConv(len(self.nonterminals), self.opts.embedding_dim)
        elif self.opts.num_message_layers == 2:
            self.conv = nn.Sequential(
                SAGEConv(len(self.nonterminals), self.opts.embedding_dim),
                nn.Dropout(self.opts.dropout),
                nn.ReLU(),
                SAGEConv(self.opts.embedding_dim, self.opts.embedding_dim)
            )
        elif self.opts.num_message_layers == 4:
            self.conv = nn.Sequential(
                SAGEConv(len(self.nonterminals), self.opts.embedding_dim),
                nn.Dropout(self.opts.dropout),
                nn.ReLU(),
                SAGEConv(self.opts.embedding_dim, self.opts.embedding_dim),
                nn.Dropout(self.opts.dropout),
                nn.ReLU(),           
                SAGEConv(self.opts.embedding_dim, self.opts.embedding_dim),     
                nn.Dropout(self.opts.dropout),
                nn.ReLU(),
                SAGEConv(self.opts.embedding_dim, self.opts.embedding_dim)              
            )
            
        if self.opts.hops > 1:
            self.internal_conv = SAGEConv(self.opts.embedding_dim, self.opts.embedding_dim) 
        
        if self.opts.pooling == "set2set":
            self.pooler = Set2Set(self.opts.embedding_dim, 2)
            
        if self.opts.node_pooling == "topk":
            self.node_pooler = TopKPooling(self.opts.embedding_dim, ratio=0.5)
            
        if self.opts.norm == "gsn":
            self.norm = GraphSizeNorm()
            
        self.dropout = nn.Dropout(self.opts.dropout)
        self.activation = nn.Tanh()
                    
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

            # node embeddings
            try:
                x = self.conv(x, edge_index)
                x = self.activation(x)
                x = self.dropout(x)
                for i in range(1, self.opts.hops):
                    x = self.internal_conv(x, edge_index)
                    x = self.activation(x)
                    x = self.dropout(x)
                if self.opts.norm != "none":
                    x = self.norm(x, batch.batch)
            except Exception as e:
                print(e)
                all_empty = []
                for i, ast in enumerate(asts):
                    all_empty.append(torch.zeros(self.opts.embedding_dim).to(self.opts.device))
                return torch.stack(all_empty)
            
            if self.opts.node_pooling != "none":
                res = self.node_pooler(x=x, edge_index=edge_index, batch=batch.batch)
                x = res[0]
                edge_index = res[1]
                batch.batch = res[3]
                            
            if self.opts.pooling == "mean":
                x = global_mean_pool(x, batch.batch)
            elif self.opts.pooling == "max":
                x = global_max_pool(x, batch.batch)
            elif self.opts.pooling == "add":
                x = global_add_pool(x, batch.batch)
            elif self.opts.pooling == "sort":
                x = global_sort_pool(x, batch.batch, 50)
                x = self.activation(x)
            elif self.opts.pooling == "set2set":
                print(x.size())
                x = self.pooler(x, batch.batch)
                x = self.activation(x)
            else:
                return "ERROR NO POOL"
            return x

        all_empty = []
        for i, ast in enumerate(asts):
            all_empty.append(torch.zeros(self.opts.embedding_dim).to(self.opts.device))

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