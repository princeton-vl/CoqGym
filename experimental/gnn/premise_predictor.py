import torch
import torch.nn as nn

class PremisePredictor(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts
    

    def get_premise_space(self, env, local_context, goal):
        pass