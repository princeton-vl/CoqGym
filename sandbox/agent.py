import json, torch
from glob import glob
from eval_env import FileEnv
from utils import SexpCache
from gallina import GallinaTermParser
import torch.nn as nn
from ffn.tacmodel import FFNTacModel
from ffn.argmodel import FFNArgModel
from graphviz import Digraph
from progressbar import ProgressBar
from hashlib import sha1


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
    def __init__(self, opts, tacmodel, argmodel):
        self.opts = opts
        self.split = json.load(open(self.opts.split, "r"))
        self.term_parser = GallinaTermParser(caching=True)
        self.sexp_cache = SexpCache(self.opts.sexp_cache, readonly=True)
        self.tactics = json.load(open(self.opts.tactics))
        self.tacmodel = tacmodel
        self.argmodel = argmodel
        self.softmax = nn.Softmax(dim=1)
    
    
    '''--- TRAIN AND VALIDATION ---'''
    def train_val(self, batch):
        if self.opts.argmodel:
            preds, trues, loss, num_correct, total_count = self.tacmodel(batch)
            print(num_correct/total_count)
            print(loss)
            print(preds)
        else:
            preds, trues, loss = self.argmodel(batch)
        return preds, trues, loss
    '''-------'''
        
        
    '''--- TESTING ---''' 
    def test(self, proof_env):
        res, graph, script = self.prove_DFS(proof_env)
        print(f"{res}, {script}")
        return {"proved": res, "graph": graph, "script": script}
        
        
    def prove_DFS(self, proof_env):
        state = proof_env.init()
        global_env = self.process_global_env(state)
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
        local_context, goal = local_envs[0]["local_context"], local_envs[0]["goal"]
        
        tactic_probs = self.tacmodel.prove(goal, local_context, global_env)
        topk, indices = torch.topk(input=tactic_probs, k=self.opts.num_tac_candidates, dim=0, largest=False)
        stack = [[self.tactics[index] for index in indices]]
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
                tac = stack[-1].pop()
                        
            if "fg_goals" in state:
                current_sign = graph_id(state)
                current_texts = graph_text(state)
            
            if tac == "intro":
                tac = "intros"
            if self.opts.tac_on_all_subgoals:
                tac = f"all: {tac}"
                
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
                
                
                node_ids.add(sig)
                local_envs = self.process_local_env(state)
                local_context, goal = local_envs[0]["local_context"], local_envs[0]["goal"]
                
                if self.opts.draw:  
                    text = graph_text(state)
                    graph.node(str(sig), text)
                    graph.edge(str(current_sign), str(sig), tac, color=edge_colors[color_index])
                
                just_moved = False
                tactic_probs = self.tacmodel.prove(goal, local_context, global_env)
                topk, indices = torch.topk(input=tactic_probs, k=self.opts.num_tac_candidates, dim=0, largest=True)
                stack.append([self.tactics[index] for index in indices])

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
    
    def add_local_envs(self, local_envs, state):
        new_local_envs = self.process_local_env(state)
        texts = [l["goal"]["text"] for l in local_envs]
        for local_env in new_local_envs:
            if local_env["goal"]["text"] not in texts:
                local_envs.append(local_env)
        
        return local_envs
    '''-------'''


                
                
       
        
    
