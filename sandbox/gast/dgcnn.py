import torch
import torch.nn.functional as F
from torch import nn
from torch.nn import Conv1d, MaxPool1d, Linear, Dropout
from torch_geometric.nn import GCNConv, global_sort_pool
from torch_geometric.utils import remove_self_loops
from helpers import traverse_postorder, get_node_count_ast
from torch_geometric.data import Data, Batch


class Model(nn.Module):
    def __init__(self, opts, num_features, num_classes, nonterminals):
        super(Model, self).__init__()
        self.opts = opts
        self.nonterminals = nonterminals

        self.conv1 = GCNConv(num_features, 32)
        self.conv2 = GCNConv(32, 32)
        self.conv3 = GCNConv(32, 32)
        self.conv4 = GCNConv(32, 1)
        self.conv5 = Conv1d(1, 16, 97, 97)
        self.conv6 = Conv1d(16, 32, 5, 1)
        self.pool = MaxPool1d(2, 2)
        self.classifier_1 = Linear(352, 128)
        self.drop_out = Dropout(0.5)
        self.classifier_2 = Linear(128, num_classes)
        self.relu = nn.ReLU(inplace=True)

    def forward(self, asts):
        x, edge_index, batch = self.prep_asts(asts)
        edge_index, _ = remove_self_loops(edge_index)

        x_1 = torch.tanh(self.conv1(x, edge_index))
        x_2 = torch.tanh(self.conv2(x_1, edge_index))
        x_3 = torch.tanh(self.conv3(x_2, edge_index))
        x_4 = torch.tanh(self.conv4(x_3, edge_index))
        x = torch.cat([x_1, x_2, x_3, x_4], dim=-1)
        x = global_sort_pool(x, batch, k=30)
        x = x.view(x.size(0), 1, x.size(-1))
        x = self.relu(self.conv5(x))
        x = self.pool(x)
        x = self.relu(self.conv6(x))
        x = x.view(x.size(0), -1)
        out = self.relu(self.classifier_1(x))
        out = self.drop_out(out)
        classes = F.log_softmax(self.classifier_2(out), dim=-1)

        return classes
        
        
    def prep_asts(self, asts):
        graph_list = []
        for i, ast in enumerate(asts):
            if ast != None:
                edge_index = self.create_edge_index(ast)
                x = self.one_hot_encode(ast)
                data = Data(x=x, edge_index=edge_index).to(self.opts.device)
                graph_list.append(data)
                
        batch = Batch().from_data_list(graph_list)
        return batch.x, batch.edge_index, batch.batch


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