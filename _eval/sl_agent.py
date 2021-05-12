from agent import Agent
import torch, json

from _SL.nn_model.gast_tac import GastTac
from _SL.nn_model.gast_lc import GastLC
from _SL.nn_model.gast_gc import GastGC

from _SL.nn_model.trans_tac import TransTac
from _SL.nn_model.trans_lc import TransLC
from _SL.nn_model.trans_gc import TransGC


class SLAgent(Agent):

    def __init__(self, opts, log):
        super().__init__(opts)

        if opts.model_type == "rl":
            self.tacmodel = GastTac(opts)
            self.lcmodel = GastLC(opts)
            self.gcmodel = GastGC(opts)
            tacmodel_path = "../_SL/models/best/acc/human/gast_tac.pth"
            lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
            gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"
            
        else:
            if "gast" in opts.sl_model:
                self.tacmodel = GastTac(opts)
                self.lcmodel = GastLC(opts)
                self.gcmodel = GastGC(opts)
                if "gast_human" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/human/gast_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/human/gast_gc.pth"
                elif "gast_all" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/all/gast_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/all/gast_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/all/gast_gc.pth"
                elif "gast_synthetic" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/synthetic/gast_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/synthetic/gast_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"
                elif "gast_overall" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/synthetic/gast_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"

            elif "trans" in opts.sl_model:
                self.tacmodel = TransTac(opts)
                self.lcmodel = TransLC(opts)
                self.gcmodel = TransGC(opts)
                if "trans_human" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/human/trans_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/human/trans_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/human/trans_gc.pth"
                elif "trans_all" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/all/trans_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/all/trans_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/all/trans_gc.pth"
                elif "trans_synthetic" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/synthetic/trans_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/synthetic/trans_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/synthetic/trans_gc.pth"
                elif "trans_overall" in opts.sl_model:
                    tacmodel_path = "../_SL/models/best/acc/synthetic/trans_tac.pth"
                    lcmodel_path = "../_SL/models/best/acc/human/trans_lc.pth"
                    gcmodel_path = "../_SL/models/best/acc/synthetic/trans_gc.pth"

            elif "best_human" in opts.sl_model:
                self.tacmodel = TransTac(opts)
                self.lcmodel = GastLC(opts)
                self.gcmodel = GastGC(opts)
                tacmodel_path = "../_SL/models/best/acc/human/trans_tac.pth"
                lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
                gcmodel_path = "../_SL/models/best/acc/human/gast_gc.pth"
            elif "best_all" in opts.sl_model:
                self.tacmodel = TransTac(opts)
                self.lcmodel = GastLC(opts)
                self.gcmodel = GastGC(opts)
                tacmodel_path = "../_SL/models/best/acc/all/trans_tac.pth"
                lcmodel_path = "../_SL/models/best/acc/all/gast_lc.pth"
                gcmodel_path = "../_SL/models/best/acc/all/gast_gc.pth"
            elif "best_synthetic" in opts.sl_model:
                self.tacmodel = TransTac(opts)
                self.lcmodel = GastLC(opts)
                self.gcmodel = GastGC(opts)
                tacmodel_path = "../_SL/models/best/acc/synthetic/trans_tac.pth"
                lcmodel_path = "../_SL/models/best/acc/synthetic/gast_lc.pth"
                gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"
            elif "best_overall" in opts.sl_model:
                self.tacmodel = TransTac(opts)
                self.lcmodel = GastLC(opts)
                self.gcmodel = GastGC(opts)
                tacmodel_path = "../_SL/models/best/acc/synthetic/trans_tac.pth"
                lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
                gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"

    
        log.info(self.tacmodel)
        log.info(self.lcmodel)
        log.info(self.gcmodel)

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
        
        log.info(f"\nloading from\n{tacmodel_path}\n{lcmodel_path}\n{gcmodel_path}")

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
