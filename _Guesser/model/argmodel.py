import os, sys, json
sys.path.append(os.path.abspath('../'))

import torch
import torch.nn.functional as F

class GuesserArgModel():
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        with open(self.opts.args) as f: self.args = json.load(f)
    
    def prove(self, goal, lc, gc):
        lc_ids = [c["ident"] for c in lc]
        gc_ids = [c["qualid"] for c in gc]
        count = len(lc_ids) + len(gc_ids) + len(self.args)
        guesses = torch.rand(count)
        probs = F.softmax(guesses, dim=0)
        return probs
            