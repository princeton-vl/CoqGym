import torch
import torch.nn as nn
import torch.nn.functional as F
import torch_geometric.nn as gnn
from torch_geometric.data import Data, Batch
from torch_geometric.nn import GCNConv, SGConv
from gallina import traverse_postorder
from utils import get_node_count_ast
from torch.nn import Sequential as Seq, Linear as Lin, ReLU


class TermEmbedder(gnn.MessagePassing):
    def __init__(self, opts, nonterminals):
        super().__init__(aggr="max")
        self.opts = opts
        self.nonterminals = nonterminals
        self.mlp = Lin(self.opts.term_embedding_dim, self.opts.term_embedding_dim)
        self.conv1 = SGConv(len(self.nonterminals), self.opts.term_embedding_dim, K=4)
        #self.conv2 = SGConv(self.opts.term_embedding_dim, self.opts.term_embedding_dim, K=4)
        #self.conv1 = GCNConv(1, self.opts.term_embedding_dim)


    def forward(self, asts):
        embeddings = []
        graph_list = []
        for i, ast in enumerate(asts):
            if ast != None:
                edge_index = self.create_edge_index(ast)
                x = self.one_hot_encode(ast)
                data = Data(x=x, edge_index=edge_index)
                graph_list.append(data)
        if graph_list:
            batch = Batch().from_data_list(graph_list)
            #emb = torch.tensor(self.propagate(x = batch.x, edge_index=batch.edge_index))
            emb = torch.tensor(self.conv1(x = batch.x, edge_index=batch.edge_index))
            #emb = torch.tensor(self.conv2(x = emb, edge_index=batch.edge_index))
            emb = self.mlp(emb)
            
        j = 0
        for i, ast in enumerate(asts):
            if ast != None:
                node_count = get_node_count_ast(ast)
                current_embeddings = emb[j: j + node_count]
                embeddings.append(F.relu(current_embeddings.sum(0))) # 'sum(0)' is the readout (e.i, turn into fixed sized vector)
                j+=node_count
            else:
                embeddings.append(torch.zeros(self.opts.term_embedding_dim))

        return torch.stack(embeddings)

    
    def message(self, x_i):
          # shape [E, 2 * F_in]
        return self.mlp(x_i)  # shape [E, F_out]

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
