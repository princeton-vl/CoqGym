import torch
import torch.nn as nn
from torch.nn import Sequential as Seq, Linear as Lin, ReLU
import torch_geometric.nn as gnn
from torch_geometric.data import Data
from torch_geometric.data import DataLoader
from gallina import traverse_postorder
from torch_geometric.nn import GCNConv
import torch.nn.functional as F


nonterminals = [
    "constr__constr",
    "constructor_rel",
    "constructor_var",
    "constructor_meta",
    "constructor_evar",
    "constructor_sort",
    "constructor_cast",
    "constructor_prod",
    "constructor_lambda",
    "constructor_letin",
    "constructor_app",
    "constructor_const",
    "constructor_ind",
    "constructor_construct",
    "constructor_case",
    "constructor_fix",
    "constructor_cofix",
    "constructor_proj",
    "constructor_ser_evar",
    "constructor_prop",
    "constructor_set",
    "constructor_type",
    "constructor_ulevel",
    "constructor_vmcast",
    "constructor_nativecast",
    "constructor_defaultcast",
    "constructor_revertcast",
    "constructor_anonymous",
    "constructor_name",
    "constructor_constant",
    "constructor_mpfile",
    "constructor_mpbound",
    "constructor_mpdot",
    "constructor_dirpath",
    "constructor_mbid",
    "constructor_instance",
    "constructor_mutind",
    "constructor_letstyle",
    "constructor_ifstyle",
    "constructor_letpatternstyle",
    "constructor_matchstyle",
    "constructor_regularstyle",
    "constructor_projection",
    "bool",
    "int",
    "names__label__t",
    "constr__case_printing",
    "univ__universe__t",
    "constr__pexistential___constr__constr",
    "names__inductive",
    "constr__case_info",
    "names__constructor",
    "constr__prec_declaration___constr__constr____constr__constr",
    "constr__pfixpoint___constr__constr____constr__constr",
    "constr__pcofixpoint___constr__constr____constr__constr",
]


class TermEncoder(gnn.MessagePassing):

    def __init__(self, opts):
        super().__init__(aggr='max')
        self.opts = opts
        self.conv1 = GCNConv(1, 16)
        self.conv2 = GCNConv(16, 126)
        

    def forward(self, asts):
        if len(asts) == 0:
            return [torch.zeros(len(asts), self.opts.term_embedding_dim).to(self.opts.device)]
        embeddings = []
        for i, ast in enumerate(asts):
            edge_index = self.create_edge_index(ast)
            if not len(edge_index):
                x = torch.zeros(self.opts.term_embedding_dim).to(self.opts.device)
            else:
                x = self.create_x(ast)
                x = self.conv1(x, edge_index)
                x = F.relu(x)
                x = F.dropout(x, training=self.training)
                x = self.conv2(x, edge_index)
                x = x.flatten()
                reshaper = nn.Linear(len(x), self.opts.term_embedding_dim)
                x = reshaper(x)

            embeddings.append(x)
        return embeddings

    def message(self, x_i, x_j):
        # x_i has shape [E, F_in]
        # x_j has shape [E, F_in]
        edge_features = torch.cat([x_i, x_j - x_i], dim=1)  # shape [E, 2 * F_in]
        return self.mlp(edge_features)  # shape [E, F_out]

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
            x.append([nonterminals.index(node.data)])
        
        traverse_postorder(ast, callbck)

        return torch.tensor(x, dtype=torch.float)
        