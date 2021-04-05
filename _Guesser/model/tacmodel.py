import os, sys, json
sys.path.append(os.path.abspath('../'))
from random import randrange
import torch
import torch.nn.functional as F

class GuesserTacModel():
    def __init__(self, opts):
        self.opts = opts
        self.tactics = json.load(open(self.opts.tactics))
    
    def prove(self):
        guesses = torch.rand(len(self.tactics))
        probs = F.softmax(guesses, dim=0)
        return probs
