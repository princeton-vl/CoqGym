from agent import Agent
import torch, json


from _RL.nn_model.q import Q
from _SL.nn_model.gast_lc import GastLC
from _SL.nn_model.gast_gc import GastGC


class RLAgent(Agent):

    def __init__(self, opts, log):
        super().__init__(opts)
        
        if opts.rl_model == "rl":
            tacmodel_path = "../_RL/models/rl_q.pth"
        elif opts.rl_model == "im":
            tacmodel_path = "../_RL/models/im_q.pth"
        elif opts.rl_model == "rl5":
            tacmodel_path = "../_RL/models/rl5_q.pth"
        elif opts.rl_model == "im5":
            tacmodel_path = "../_RL/models/im5_q.pth"
        lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
        gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"

        self.tacmodel = Q(opts)
        self.lcmodel = GastLC(opts)
        self.gcmodel = GastGC(opts)
        if opts.device.type == "cpu":
            taccheck = torch.load(tacmodel_path, map_location="cpu")
            lccheck = torch.load(lcmodel_path, map_location="cpu")
            gccheck = torch.load(gcmodel_path, map_location="cpu")
        else:
            taccheck = torch.load(tacmodel_path)
            lccheck = torch.load(lcmodel_path)
            gccheck = torch.load(gcmodel_path)
        self.tacmodel.load_state_dict(taccheck["state_dict"])
        self.lcmodel.load_state_dict(lccheck["state_dict"])
        self.gcmodel.load_state_dict(gccheck["state_dict"])
        self.tacmodel.to(opts.device)
        self.lcmodel.to(opts.device)
        self.gcmodel.to(opts.device)
        self.tacmodel.eval()
        self.lcmodel.eval()
        self.gcmodel.eval()

    def get_candidates(self):
        goal, lc, gc = self.state[0], self.state[1], self.state[2]
        tactic_probs = self.tacmodel.prove(goal, lc, gc)
        topk, indices = torch.topk(input=tactic_probs, k=self.opts.num_tac_candidates, dim=0, largest=True)
        arg_probs = self.get_arg_probs(goal, lc, gc)

        res = []
        for index in indices:
            tac = self.tactics[index]
            tac = self.prep_tac(tac, arg_probs)
            res.append(tac)

        return res

    def get_arg_probs(self, goal, lc, gc):
        gcprobs = self.gcmodel.prove(goal, lc, gc)
        lcprobs = self.lcmodel.prove(goal, lc, gc)

        lc_ids = [c["ident"] for c in lc]
        gc_ids = [c["qualid"] for c in gc]
        
        res = {"lc": {}, "gc": {}}
        for i in range(10):
            if i >= len(gc_ids):
                res["gc"][gcprobs[i]] = ""
            else:
                res["gc"][gcprobs[i]] = gc_ids[i]

        for i in range(10):
            if i >= len(lc_ids):
                res["lc"][lcprobs[i]] = ""
            else:
                res["lc"][lcprobs[i]] = lc_ids[i]
                   
        return res

    def prep_tac(self, tactic, arg_probs):
        gc_arg = arg_probs["gc"][max(arg_probs["gc"].keys())]
        lc_arg = arg_probs["lc"][max(arg_probs["lc"].keys())]      

        # froced theorem
        if tactic in ["apply", "rewrite", "unfold", "destruct", "elim", "case", "generalize", "exact"]:
            tactic = f"{tactic} {gc_arg}"

        # forced assumption
        elif tactic in ["induction", "exists", "revert", "inversion_clear", "injection", "contradict"]:
            tactic = f"{tactic} {lc_arg}"

        return tactic
