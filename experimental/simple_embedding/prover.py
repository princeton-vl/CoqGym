import torch
import torch.nn as nn
from .tactic_predictor import TacticPredictor
import json

class TermEmbedder(nn.Embedding):
    def __init__(self, opts):
        super().__init__(num_embeddings=1, embedding_dim=opts.term_embedding_dim)
        self.opts = opts



class Prover(nn.Module):

    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        with open('./tactic_space.json', 'r') as f:
            self.tactic_space = json.load(f)[self.opts.tactic_space]
        self.tactic_predictor = TacticPredictor(self.opts, self.tactic_space)
        self.term_embedder = TermEmbedder(self.opts)

    def forward(self, batch):
        batchsize = self.opts.batchsize
        gc, lc, goals, tactics = self.get_texts(batch)

        lc_embeddings = []
        for i, current_lc in enumerate(lc):
            temp = []
            for term in current_lc:
                current_embedding = self.embedd(term)
                temp.append(current_embedding)
            lc_embeddings.append(temp)

        goal_embeddings = []
        for i, current_goal in enumerate(goals):
            current_embedding = self.embedd(current_goal)
            goal_embeddings.append(current_embedding)

        print(lc_embeddings)
        print(goal_embeddings)


    def embedd(self, text):
        return self.term_embedder(text)
        

    def get_texts(self, batch):
        goals = batch['goal_text']

        gc = []
        for current_gc in batch['env']:
            temp = []
            for term in current_gc:
                temp.append(term['qualid'])
            gc.append(temp)

        lc = []
        for current_lc in batch['local_context']:
            temp = []
            for term in current_lc:
                temp.append(term['text'])
            lc.append(temp)

        tactics = batch['tactic_str']
        return gc, lc, goals, tactics