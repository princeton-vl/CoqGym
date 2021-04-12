import os, sys, json
sys.path.append(os.path.abspath('../'))
from random import randrange
import torch
import torch.nn.functional as F

class GuesserTacModel():
    def __init__(self, opts):
        self.opts = opts
        with open(self.opts.tactics) as f: self.tactics = json.load(f)
    
    def prove(self, goal, lc, gc):
        guesses = torch.rand(len(self.tactics))
        probs = F.softmax(guesses, dim=0)
        return probs
