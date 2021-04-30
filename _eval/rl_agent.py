from agent import Agent
import torch, json
from _RL.nn_model.q import Q

class RLAgent(Agent):

    def __init__(self, opts, log):
        super().__init__(opts)
        self.Q = Q(opts)
        
        log.info(self.Q)

        if opts.rl_model == "rl":
            model_path = "../_RL/models/rl_q000.pth"
        elif opts.rl_model == "im_a":
            model_path = "../_RL/models/im_a_q000.pth"
        elif opts.rl_model == "im_s":
            model_path = "../_RL/models/im_s_q000.pth"
        elif opts.rl_model == "im_h":
            model_path = "../_RL/models/im_h_q000.pth"
        
        log.info(f"loading from {model_path}")

        if opts.device.type == "cpu":
            check = torch.load(model_path, map_location="cpu")
        else:
            check = torch.load(model_path)
        
        self.Q.load_state_dict(check["state_dict"])
        self.Q.to(opts.device)
        self.Q.eval()

    def get_candidates(self):
        actions = self.get_actions()
        q_values = self.Q(self.state)

        topk, indices = torch.topk(input=q_values, k=10, dim=0, largest=True)
        candidates = []
        for i in indices:
            candidates.append(actions[i])
        return candidates


    def get_actions(self):
        goal, lc, gc = self.state[0], self.state[1], self.state[2]        
        with open(self.opts.tactics_sorted) as f: tactics_sorted = json.load(f)
        non_args = tactics_sorted['non_args']
        gc_args = tactics_sorted['gc_args']
        lc_args = tactics_sorted['lc_args']

        res = []
        for tactic in non_args:
            tmp = self.prep_tac(tactic, lc, gc)
            res += tmp
        for tactic in lc_args:
            tmp = self.prep_tac(tactic, lc, gc)
            res += tmp
        for tactic in gc_args:
            tmp = self.prep_tac(tactic, lc, gc)
            res += tmp

        assert len(res) == self.opts.action_space
        return res

    def prep_tac(self, tactic, lc, gc):
        res = []

        # froced theorem
        if tactic in ['apply', 'rewrite', 'unfold', 'destruct', 'elim', 'case', 'generalize', 'exact']:
            i = 0
            while len(res) < 10:
                if i < len(gc):
                    res.append(f"{tactic} {gc[i]['ident']}")
                else:
                    res.append(f"{tactic} NONE")
                i += 1            

        # forced assumption
        elif tactic in ['induction', 'exists', 'revert', 'inversion_clear', 'injection', 'contradict']:
            i = 0
            while len(res) < 20:
                if i < len(lc):
                    res.append(f"{tactic} {lc[i]['ident']}")
                else:
                    res.append(f"{tactic} NONE")
                i += 1
        else:
            res.append(tactic)
    
        return res
