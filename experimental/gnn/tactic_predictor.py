import torch
import torch.nn as nn


simple_tactic_space = ["intro",
                "intros",
                "split",
                "assumption",
                "trivial",
                "reflexivity",
                "omega",
                "congruence",
                "left",
                "right",
                "ring",
                "symmetry",
                "f_equal",
                "tauto",
                "idtac",
                "exfalso",
                "cbv",
                "lia",
                "field",
                "easy",
                "cbn",
                "intuition",
                "OTHER"
]

class TacticPredictor(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.predictor = nn.Linear(259, 23)
        self.categories = simple_tactic_space

    def forward(self, global_context, local_context, goal):
        goal_embeddings = goal["embeddings"]
        pred = self.predictor(goal_embeddings)
        return torch.softmax(pred, dim=1)
