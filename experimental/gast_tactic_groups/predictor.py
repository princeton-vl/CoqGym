import torch.nn as nn
import torch.nn.functional as F

class Predictor(nn.Module):
    def __init__(self, opts, tactic_groups):
        super().__init__()
        self.opts = opts
        self.tactic_groups = tactic_groups
        self.lin1 = nn.Linear(3*opts.term_embedding_dim, 500)
        self.lin2 = nn.Linear(500, 500)
        self.lin3 = nn.Linear(500, 400)
        self.lin4 = nn.Linear(400, 300)
        self.lin5 = nn.Linear(300, 200)
        self.lin6 = nn.Linear(200, len(tactic_groups))
        self.droput = nn.Dropout(self.opts.dropout_rate)
        self.softmax = nn.Softmax()

    def forward(self, embeddings):
        x = F.relu(self.lin1(embeddings))
        x = self.droput(x)
        x = F.relu(self.lin2(x))
        x = self.droput(x)
        x = F.relu(self.lin3(x))
        x = self.droput(x)
        x = F.relu(self.lin4(x))
        x = self.droput(x)
        x = F.relu(self.lin5(x))
        x = self.droput(x)
        x = self.lin6(x)
        x = self.droput(x)
        x = self.softmax(x)
        return x