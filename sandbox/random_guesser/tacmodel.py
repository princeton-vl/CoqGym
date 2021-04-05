import os, sys, json
sys.path.append(os.path.abspath('../'))
from gallina import traverse_postorder
from random import randrange
import torch
import torch.nn.functional as F
from helpers import get_tactic_targets, get_true_tactics, get_true_args, get_pred_tactics

class GuesserTacModel():
    def __init__(self, opts):
        self.opts = opts
        self.tactics = json.load(open(self.opts.tactics))
    
    def prove(self, goal, local_context, global_context):
        guesses = torch.rand(len(self.tactics))
        probs = F.softmax(guesses, dim=0)
        return probs
        
        
        
        
        