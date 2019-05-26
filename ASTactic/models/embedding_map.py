import torch
import torch.nn as nn

class EmbeddingMap(nn.Module):

    def __init__(self, dim, opts):
        self.dim = dim
        self.opts = opts
        self.mapping = {}

    def __getitem__(self, key):
        if key not in self.mapping:
            embedding = nn.Parameters(torch.Tensor(self.dim).to(self.opts.device))
            nn.init.normal_(embedding, std=0.1)
            self.mapping[key] = embedding
            self.register_parameter(key, embedding)
        return self.mapping[key]
