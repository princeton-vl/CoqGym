import random, torch
import torch.nn as nn

class RandomTac:
    def __init__(self):
        self.softmax = nn.Softmax(dim=-1)

    def prove(self, goal, lc, gc):
        res = []
        for i in range(49):
            res.append(random.uniform(0, 1))
        return self.softmax(torch.FloatTensor(res))

class RandomLC:
    def __init__(self):
        self.softmax = nn.Softmax(dim=-1)

    def prove(self, goal, lc, gc):
        res = []
        for i in range(10):
            res.append(random.uniform(0, 1))
        return self.softmax(torch.FloatTensor(res))

class RandomGC:
    def __init__(self):
        self.softmax = nn.Softmax(dim=-1)
    def prove(self, goal, lc, gc):
        res = []
        for i in range(10):
            res.append(random.uniform(0, 1))
        return self.softmax(torch.FloatTensor(res))