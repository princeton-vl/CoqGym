import torch
import torch.nn as nn
from experimental.gnn.term_encoder import TermEncoder
from experimental.gnn.tactic_predictor import TacticPredictor
from itertools import chain


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

class Prover(nn.Module):
   
    def __init__(self, opts):
        super().__init__()
        self.opts = opts
        self.term_encoder = TermEncoder(opts)
        self.tactic_predictor = TacticPredictor(opts)


    def forward(self, global_context, local_context, goal, actions):
        # compute embeddings
        global_embeddings, local_embeddings, goal_embeddings = self.embed_terms(global_context, local_context, goal)
        global_prepped, local_prepped, goal_prepped = self.format(global_context, 
                                                global_embeddings,
                                                local_context,
                                                local_embeddings,
                                                goal,
                                                goal_embeddings)
        
        # predict tactics
        predictions = self.fnn_prediction(global_prepped, local_prepped, goal_prepped)
        print(predictions)
        # compute losses
        loss = self.compute_loss(predictions, actions)
        
        return loss


    def embed_terms(self, global_context, local_context, goal):

        all_asts = list(
            chain(
                [env["ast"] for env in chain(*global_context)],
                [context["ast"] for context in chain(*local_context)],
                goal,
            )
        )

        all_embeddings = self.term_encoder(all_asts)

        batchsize = len(global_context)
        global_embeddings = []
        j = 0
        for n in range(batchsize):
            size = len(global_context[n])
            global_embeddings.append(
                torch.cat(
                    [
                        torch.zeros(size, 3, device=self.opts.device),
                        all_embeddings[j : j + size],
                    ],
                    dim=1,
                )
            )
            global_embeddings[-1][:, 0] = 1.0
            j += size

        local_embeddings = []
        for n in range(batchsize):
            size = len(local_context[n])
            local_embeddings.append(
                torch.cat(
                    [
                        torch.zeros(size, 3, device=self.opts.device),
                        all_embeddings[j : j + size],
                    ],
                    dim=1,
                )
            )
            local_embeddings[-1][:, 1] = 1.0
            j += size

        goal_embeddings = []
        for n in range(batchsize):
            goal_embeddings.append(
                torch.cat(
                    [torch.zeros(3, device=self.opts.device), all_embeddings[j]], dim=0
                )
            )
            goal_embeddings[-1][2] = 1.0
            j += 1

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


    def fnn_prediction(self, global_embedding, local_embedding, goal_embedding):
        return self.tactic_predictor(global_embedding, local_embedding, goal_embedding)


    def compute_loss(self, tactic_predictions, tactic_true):
        target = self.tactic_space_mapping(tactic_true)
        criterion = nn.CrossEntropyLoss()
        loss = criterion(tactic_predictions, target)
        print(loss)
        return loss
    

    def tactic_space_mapping(self, actions):
        target = torch.empty(self.opts.batchsize, dtype=torch.long)
        for i, action in enumerate(actions):
            if action in simple_tactic_space:
                index = simple_tactic_space.index(action)
            else:
                index = 22
            target[i] = index

        return target
