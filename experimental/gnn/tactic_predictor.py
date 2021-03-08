import torch
import torch.nn as nn

class TacticPredictor(nn.Module):

    def __init__(self, opts, tactic_space):
        super().__init__()
        self.opts = opts
        self.predictor = nn.Linear(opts.term_embedding_dim, 2)
        self.tactic_space = tactic_space

    def forward(self, global_context, local_context, goal):
        goal_embeddings = goal["embeddings"]
        pred = self.predictor(goal_embeddings)
        return torch.softmax(pred, dim=1)
        