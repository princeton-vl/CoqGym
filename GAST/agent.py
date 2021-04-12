import json, torch
from glob import glob
from eval_env import FileEnv
from utils import SexpCache
from gallina import GallinaTermParser
import torch.nn as nn
from graphviz import Digraph
from progressbar import ProgressBar
from hashlib import sha1
from helpers import prep_tac


def graph_text(obs):
    if "fg_goals" not in obs:
        return "NO GOALS"
    
    res = ""
    for g in obs["fg_goals"]:
        text = g["type"]
        res = f"{res}{text}\n"
    return res
    
def graph_id(obs):    
    res = ""
    for g in obs["fg_goals"]:
        sign = get_goal_signature(g)
        res = f"{res}{sign}"
    return res
    
def node_id(obs):
    res = set()
    for g in obs["fg_goals"]:
        sign = get_goal_signature(g)
        res.add(sign)
    return frozenset(res)
    
    
def print_single_goal(g):
    for h in g["hypotheses"]:
        for ident in h["idents"]:
            print("\t%s: %s" % (ident, h["type"]))
    print("---------------")
    print("\t%s" % g["type"])
    print("##########")

def print_goals(obs):
    if "fg_goals" not in obs:
        print("##########")
        return
    print("########## fg_goals ##########")
    for g in obs["fg_goals"]:
        print_single_goal(g)
    print("########## bg_goals ##########")
    for g in obs["bg_goals"]:
        print_single_goal(g)
    print("########## shelved_goals ##########")
    for g in obs["shelved_goals"]:
        print_single_goal(g)
    print("########## given_up_goals ##########")
    for g in obs["given_up_goals"]:
        print_single_goal(g)
        
def get_goal_signature(goal):
    sexp = goal["sexp"] + "".join([h["sexp"] for h in goal["hypotheses"]])
    return sha1(sexp.encode("utf-8")).hexdigest()

class Agent:
    def __init__(self, opts, tacmodel, lcmodel, gcmodel):
        self.opts = opts
        self.split = json.load(open(self.opts.split, "r"))
        self.term_parser = GallinaTermParser(caching=True)
        self.sexp_cache = SexpCache(self.opts.sexp_cache, readonly=True)
        self.tactics = json.load(open(self.opts.tactics))
        self.tacmodel = tacmodel
        self.lcmodel = lcmodel
        self.gcmodel = gcmodel
        self.softmax = nn.Softmax(dim=1)
        self.greylist = ["induction", "apply", "generalize", "destruct", "elim", "rewrite", "inversion_clear"]
        
    def test(self, proof_env):
        res, graph, script = self.prove_DFS(proof_env)
        print(f"{res}, {script}")
        return {"proved": res, "graph": graph, "script": script}
        
    def prove_DFS(self, proof_env):
        used_tacs = set()
        state = proof_env.init()
        gc = self.process_global_env(state)
        node_ids = set() # keep track of all nodes seen so far
        root_id = graph_id(state)
        node_ids.add(root_id)
        
        # setup graph
        if self.opts.draw:
            color_index = 0
            edge_colors = ["red", "green", "yellow", "blue", "brown", "black"]
            just_moved = False
            text = graph_text(state)
            current_sign = graph_id(state)
            graph = Digraph()
            graph.node(str(current_sign), text)
        else:
            graph = None
            
        # initialize the stack
        local_envs = self.process_local_env(state)
        lc, goal = local_envs[0]["local_context"], local_envs[0]["goal"]
        stack = []
        stack.append(self.get_candidates(goal, lc, gc))
        script = []

        
        # depth-first search starting from the trace
        while stack != [[]]:
            # pick a tactic
            if stack[-1] == []:  # all candidate have been tried, backtrack
                stack.pop()
                script.pop()
                state = proof_env.step("Undo.")
                
                if self.opts.draw and not just_moved:
                    just_moved = True
                    color_index += 1
                    if color_index >= len(edge_colors):
                        color_index = 0
                        
                continue
            else:
                tac = stack[-1].pop(0)
                        
            if "fg_goals" in state:
                current_sign = graph_id(state)
                current_texts = graph_text(state)

            if tac in used_tacs:
                continue
            if script.count("intros") > 6 or script.count("split") > 6:
                continue
            
            
            state = proof_env.step(f"{tac}.")
            
            if state["result"] == "SUCCESS":
                if self.opts.draw:
                    text = graph_text(state)
                    graph.edge(str(current_sign), text, tac, color=edge_colors[color_index])
                
                script.append(tac)
                return True, graph, script
            elif state["result"] in ["MAX_NUM_TACTICS_REACHED", "MAX_TIME_REACHED"]:
                return False, graph, script
            elif state["result"] in ["ERROR"]:
                continue
            else:                
                assert state["result"] == "PROVING"
                script.append(tac)
                sig = graph_id(state)

                if sig in node_ids or len(script) >= self.opts.depth_limit:
                    state = proof_env.step("Undo.")
                    script.pop()
                    continue
                
                if tac.split(" ")[0] in self.greylist:
                    used_tacs.add(tac)

                node_ids.add(sig)
                local_envs = self.process_local_env(state)
                lc, goal = local_envs[0]["local_context"], local_envs[0]["goal"]

                if self.opts.draw:  
                    text = graph_text(state)
                    graph.node(str(sig), text)
                    graph.edge(str(current_sign), str(sig), tac, color=edge_colors[color_index])
                
                just_moved = False
                stack.append(self.get_candidates(goal, lc, gc))

        state = proof_env.step("Admitted.")
        return False, graph, script
    
    def process_global_env(self, state):
        global_env = []
        toplevel_consts = [const for const in state["env"]["constants"] if const["qualid"].startswith("SerTop")]
            
        for const in toplevel_consts[-10:]:
            ast = self.sexp_cache[const["sexp"]]
            global_env.append({"qualid": const["qualid"], "text": const["type"], "ast": self.term_parser.parse(ast)})
        
        return global_env
        
    def process_local_env(self, state):
        local_envs = []
        for g in state["fg_goals"]:
            goal = {"id": g["id"], "text": g["type"], "ast": self.term_parser.parse(g["sexp"])}
            local_context = []
            for i, h in enumerate(g["hypotheses"]):
                    for ident in h["idents"]:
                        local_context.append({"ident": ident, "text": h["type"], "ast": self.term_parser.parse(h["sexp"])})
            local_env = {"goal": goal, "local_context": local_context}
            local_envs.append(local_env)
        return local_envs

    def get_candidates(self, goal, lc, gc):
        tactic_probs = self.tacmodel.prove(goal, lc, gc)
        topk, indices = torch.topk(input=tactic_probs, k=self.opts.num_tac_candidates, dim=0, largest=True)
        arg_probs = self.get_arg_probs(goal, lc, gc)

        res = []
        for index in indices:
            tac = self.tactics[index]
            tac = prep_tac(self.opts, tac, arg_probs)
            res.append(tac)

        return res

    def get_arg_probs(self, goal, lc, gc):
        gcprobs = self.gcmodel.prove(goal, lc, gc)
        lcprobs = self.lcmodel.prove(goal, lc, gc)

        lc_ids = [c["ident"] for c in lc]
        gc_ids = [c["qualid"] for c in gc]
        
        res = {"lc": {}, "gc": {}}
        for i in range(10):
            if i >= len(lc_ids):
                res["lc"][lcprobs[i]] = ""
            else:
                res["lc"][lcprobs[i]] = lc_ids[i]

            if i >= len(gc_ids):
                res["gc"][gcprobs[i]] = ""
            else:
                res["gc"][gcprobs[i]] = gc_ids[i]   
                   
        return res