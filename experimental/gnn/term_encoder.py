import torch
import torch.nn as nn

class TermEncoder(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts

    def forward(self, asts):
        return torch.zeros(len(asts), self.opts.term_embedding_dim).to(self.opts.device)
        