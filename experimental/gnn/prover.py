import torch
import torch.nn as nn
from experimental.gnn.term_encoder import TermEncoder
from experimental.gnn.tactic_predictor import TacticPredictor
from experimental.gnn.premise_predictor import PremisePredictor
from itertools import chain


tactic_space = [
                "reflexivity",
                "OUT OF VOCAB"
]

class Prover(nn.Module):
   
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.term_encoder = TermEncoder(opts)
        self.tactic_predictor = TacticPredictor(opts, tactic_space)
        self.premise_predictor = PremisePredictor(opts)

    def forward(self, batch):
        
        # get goal asts
        

        # compute embeddings
        global_embedding, local_embedding, goal_embedding = self.embed_terms(global_context, local_context, goal, goal_text)
        
        global_prepped, local_prepped, goal_prepped = self.format(global_context, 
                                                global_embedding,
                                                local_context,
                                                local_embedding,
                                                goal,
                                                goal_embedding)


        # predictions
        tac_preds = self.tactic_predictor(global_prepped, local_prepped, goal_prepped)
        #arg_preds = self.premise_predictor(global_prepped, local_prepped, goal_prepped)
        
        # compute losses
        loss = self.compute_loss(tac_preds, actions)
        
        return loss


    def embed_terms(self, gc, lc, goal, goal_text):
        batch_size = len(gc)

        global_embeddings = []
        local_embeddings = []
        goal_embeddings = []
        for i in range(batch_size):
            current_gc = gc[i]
            current_lc = lc[i]
            current_goal = goal[i]
            global_asts = [env["ast"] for env in current_gc]
            local_asts = [context["ast"] for context in current_lc]
            goal_asts = [current_goal]
            ge = self.term_encoder(global_asts)
            le = self.term_encoder(local_asts)
            goal_embedding = self.term_encoder(goal_asts)
            ge = torch.cat(ge)
            le = torch.cat(le)
            global_embeddings.append(ge)
            local_embeddings.append(le)
            goal_embeddings.append(goal_embedding[0])
        
        """
        for n in range(batch_size):
            goal_embeddings[n] = torch.tens([torch.zeros(3, device=self.opts.device), goal_embeddings[n]], dim=0)
            goal_embeddings[-1][2] = 1.0
        """

        goal_embeddings = torch.stack(goal_embeddings)

        return global_embeddings, local_embeddings, goal_embeddings

    
    def format(self, global_context, global_embeddings, local_context, local_embeddings, goal, goal_embeddings):
        g_context = [
            {
                "idents": [v["qualid"] for v in env],
                "embeddings": global_embeddings[i],
                "quantified_idents": [v["ast"].quantified_idents for v in env],
            }
            for i, env in enumerate(global_context)
        ]
        l_context = [
            {
                "idents": [v["ident"] for v in context],
                "embeddings": local_embeddings[i],
                "quantified_idents": [v["ast"].quantified_idents for v in context],
            }
            for i, context in enumerate(local_context)
        ]
        goal = {
            "embeddings": goal_embeddings,
            "quantified_idents": [g.quantified_idents for g in goal],
        }
        return g_context, l_context, goal


    def compute_loss(self, tactic_predictions, tactic_true):
        target = self.tactic_space_mapping(tactic_true)
        criterion = nn.CrossEntropyLoss()
        loss = criterion(tactic_predictions, target)

        true_prediction = tactic_space[torch.argmax(tactic_predictions)]
        #print(f"\n{true_prediction} | {tactic_true}\n")

        return loss
    

    def tactic_space_mapping(self, actions):
        target = torch.empty(self.opts.batchsize, dtype=torch.long)
        for i, action in enumerate(actions):
            if action in tactic_space:
                index = tactic_space.index(action)
            else:
                index = 1
            target[i] = index

        return target
