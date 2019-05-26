import torch
import torch.nn as nn
import torch.nn.functional as F
import math
from collections import defaultdict
from time import time
from itertools import chain
from lark.tree import Tree
import os
from gallina import traverse_postorder
import pdb


nonterminals = [
    'constr__constr',
    'constructor_rel',
    'constructor_var',
    'constructor_meta',
    'constructor_evar',
    'constructor_sort',
    'constructor_cast',
    'constructor_prod',
    'constructor_lambda',
    'constructor_letin',
    'constructor_app',
    'constructor_const',
    'constructor_ind',
    'constructor_construct',
    'constructor_case',
    'constructor_fix',
    'constructor_cofix',
    'constructor_proj',
    'constructor_ser_evar',
    'constructor_prop',
    'constructor_set',
    'constructor_type',
    'constructor_ulevel',
    'constructor_vmcast',
    'constructor_nativecast',
    'constructor_defaultcast',
    'constructor_revertcast',
    'constructor_anonymous',
    'constructor_name',
    'constructor_constant',
    'constructor_mpfile',
    'constructor_mpbound',
    'constructor_mpdot',
    'constructor_dirpath',
    'constructor_mbid',
    'constructor_instance',
    'constructor_mutind',
    'constructor_letstyle',
    'constructor_ifstyle',
    'constructor_letpatternstyle',
    'constructor_matchstyle',
    'constructor_regularstyle',
    'constructor_projection',
    'bool',
    'int',
    'names__label__t',
    'constr__case_printing',
    'univ__universe__t',
    'constr__pexistential___constr__constr',
    'names__inductive',
    'constr__case_info',
    'names__constructor',
    'constr__prec_declaration___constr__constr____constr__constr',
    'constr__pfixpoint___constr__constr____constr__constr',
    'constr__pcofixpoint___constr__constr____constr__constr',
]


class InputOutputUpdateGate(nn.Module):

    def __init__(self, hidden_dim, nonlinear):
        super().__init__()
        self.nonlinear = nonlinear
        k = 1. / math.sqrt(hidden_dim)
        self.W = nn.Parameter(torch.Tensor(hidden_dim, len(nonterminals) + hidden_dim))
        nn.init.uniform_(self.W, -k, k)
        self.b = nn.Parameter(torch.Tensor(hidden_dim))
        nn.init.uniform_(self.b, -k, k)
     

    def forward(self, xh):
        return self.nonlinear(F.linear(xh, self.W, self.b))


class ForgetGates(nn.Module):

    def __init__(self, hidden_dim, opts):
        super().__init__()
        self.hidden_dim = hidden_dim
        self.opts = opts
        k = 1. / math.sqrt(hidden_dim)
        # the weight for the input
        self.W_if = nn.Parameter(torch.Tensor(hidden_dim, len(nonterminals)))
        nn.init.uniform_(self.W_if, -k, k)
        # the weight for the hidden
        self.W_hf = nn.Parameter(torch.Tensor(hidden_dim, hidden_dim))
        nn.init.uniform_(self.W_hf, -k, k)
        # the bias
        self.b_f = nn.Parameter(torch.Tensor(hidden_dim))
        nn.init.uniform_(self.b_f, -k, k)


    def forward(self, x, h_children, c_children):
        c_remain = torch.zeros(x.size(0), self.hidden_dim).to(self.opts.device)

        Wx = F.linear(x, self.W_if)
        all_h = list(chain(*h_children))
        if all_h == []:
            return c_remain
        Uh = F.linear(torch.stack(all_h), self.W_hf, self.b_f)
        i = 0
        for j, h in enumerate(h_children):
            if h == []:
                continue
            f_gates = torch.sigmoid(Wx[j] + Uh[i : i + len(h)])
            i += len(h)
            c_remain[j] = (f_gates * torch.stack(c_children[j])).sum(dim=0)
       
        return c_remain


class TermEncoder(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.input_gate = InputOutputUpdateGate(opts.term_embedding_dim, nonlinear=torch.sigmoid)
        self.forget_gates = ForgetGates(opts.term_embedding_dim, opts)
        self.output_gate = InputOutputUpdateGate(opts.term_embedding_dim, nonlinear=torch.sigmoid)
        self.update_cell = InputOutputUpdateGate(opts.term_embedding_dim, nonlinear=torch.tanh)


    def forward(self, term_asts):
        # the height of a node determines when it can be processed
        height2nodes = defaultdict(set)

        def get_height(node):
            height2nodes[node.height].add(node)

        for ast in term_asts:
            traverse_postorder(ast, get_height)

        memory_cells = {} # node -> memory cell
        hidden_states = {} # node -> hidden state
        #return torch.zeros(len(term_asts), self.opts.term_embedding_dim).to(self.opts.device)

        # compute the embedding for each node
        for height in sorted(height2nodes.keys()):
            nodes_at_height = list(height2nodes[height])
            # sum up the hidden states of the children
            h_sum = []
            c_remains = []
            x = torch.zeros(len(nodes_at_height), len(nonterminals), device=self.opts.device) \
                     .scatter_(1, torch.tensor([nonterminals.index(node.data) for node in nodes_at_height], 
                                                 device=self.opts.device).unsqueeze(1), 1.0)

            h_sum = torch.zeros(len(nodes_at_height), self.opts.term_embedding_dim).to(self.opts.device)
            h_children = []
            c_children = []
            for j, node in enumerate(nodes_at_height):
                h_children.append([])
                c_children.append([])
                for c in node.children:
                    h = hidden_states[c]
                    h_sum[j] += h
                    h_children[-1].append(h)
                    c_children[-1].append(memory_cells[c])
            c_remains = self.forget_gates(x, h_children, c_children) 

            # gates
            xh = torch.cat([x, h_sum], dim=1)
            i_gate = self.input_gate(xh)
            o_gate = self.output_gate(xh)
            u = self.update_cell(xh) 
            cells = i_gate * u + c_remains
            hiddens = o_gate * torch.tanh(cells)


            for i, node in enumerate(nodes_at_height):
                memory_cells[node] = cells[i]
                hidden_states[node] = hiddens[i]
       
        return torch.stack([hidden_states[ast] for ast in term_asts])
