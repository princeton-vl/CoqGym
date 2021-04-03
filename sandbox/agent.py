import json, torch
from glob import glob
from helpers import files_on_split
from eval_env import FileEnv
from utils import SexpCache
from gallina import GallinaTermParser
import torch.nn as nn
from ffn.tacmodel import FFNTacModel
from ffn.argmodel import FFNArgModel
from graphviz import Digraph
from progressbar import ProgressBar


class Agent:
    def __init__(self, opts, model):
        self.opts = opts
        self.split = json.load(open(self.opts.split, "r"))
        self.train_files, self.valid_files, self.test_files = files_on_split(self.opts.datapath, self.split)
        self.term_parser = GallinaTermParser(caching=True)
        self.sexp_cache = SexpCache(self.opts.sexp_cache, readonly=True)
        self.tactics = json.load(open(self.opts.tactics))
        self.model = model
        self.softmax = nn.Softmax(dim=1)
    
    
    '''--- TRAIN AND VALIDATION ---'''
    def train_val(self, batch):
        if self.opts.argmodel:
            preds, trues, loss, num_correct, total_count = self.model(batch)
            print(num_correct/total_count)
            print(loss)
            print(preds)
        else:
            preds, trues, loss = self.model(batch)
        return preds, trues, loss
    '''-------'''
        
        
    '''--- TESTING ---'''    
    def test(self):
        
        # initialize the models
        if self.opts.model == "ffn":
            self.tacmodel = FFNTacModel(self.opts)
            #argmodel = FFNArgModel(self.opts)
            
        if self.opts.device.type == "cpu":
            taccheck = torch.load(self.opts.tacmodel, map_location="cpu")
            #argcheck = torch.load(self.otps.argmodel, map_location="cpu")
        else:
            taccheck = torch.load(self.opts.tacmodel)
            #argcheck = torch.load(self.opts.argmodel)
        
        self.tacmodel.load_state_dict(taccheck["state_dict"])
        #argmodel.load_state_dict(argcheck["state_dict"])
        self.tacmodel.to(self.opts.device)
        #argmodel.to(self.opts.device)
        
        # loop over all test files
        counter = 0
        file_counter = 0
        bar = ProgressBar(max_value=len(self.test_files))
        num_correct = 0
        for f in self.test_files:
            file_counter += 1
            file_env = FileEnv(f, max_num_tactics=50, timeout=60000)
            
            # loop over all proof envs in each file
            for proof_env in file_env:
                # Single proof
                #print("-------")        
                proof_name = proof_env.proof["name"]
                #print(f"Proving: {proof_name} in {f}")
                res, script = self.prove(proof_env)
                if res:
                    num_correct += 1
                #print(f"Proved: {res}. Script: {script}")
                #print("-------")
                
                counter += 1
                
                if self.opts.lm <= counter and self.opts.lm > -1:
                    break
                
            
            print(f"\nacc: {num_correct/counter}")
            
            bar.update(file_counter)
            if self.opts.lm <= counter and self.opts.lm > -1:
                break
            
            
    def prove(self, proof_env):
        # the human proof
        # print(proof_env.proof["steps"])
        
        # start searching for proof of current proof env
        state = proof_env.init()
        
        # setup graph
        #proof_name = proof_env.proof["name"]
        #current_id = state["fg_goals"][0]["id"]
        #current_text = state["fg_goals"][0]["type"]
        #graph = Digraph()
        #graph.node(str(current_id), current_text)
        
        # setup search
        global_env = self.process_global_env(state)
        script = []
        
        # each state contains a list of open goals+assumptions -> extracting those here for the current state
        local_envs = self.process_local_env(state)
        # keep track of tried tactics
        prev_tacs = {}
        prev_evaluated = []
        while local_envs:
            ids = [l["goal"]["id"] for l in local_envs]
            prev_ids = [l["goal"]["id"] for l in prev_evaluated]
            
            
            local_env = local_envs.pop(-1)
            
            current_id = local_env["goal"]["id"]
            current_text = local_env["goal"]["text"]
            #print(current_text)
            
            prev_evaluated.append(local_env)
            prev_tacs[current_text] = prev_tacs.get(current_text, [])
            
            
            res, tactic, state = self.prove_single_local_env(proof_env, state, local_env, global_env, prev_tacs[local_env["goal"]["text"]]) 
            
            
            prev_tacs[current_text].append(tactic)
            if len(prev_tacs[current_text]) >= self.opts.num_tactics:
                prev_evaluated.remove(local_env)
            
            
            if res == "FAILED":
                if not local_envs and prev_evaluated:
                    state = proof_env.step(f"Undo.")
                    prev_evaluated.reverse()
                    local_envs = prev_evaluated
                    prev_evaluated = []
            elif res == "MAX":
                #print("MAX")
                #print(prev_tacs)
                #graph.render(f'logs/{proof_name}', view=False, quiet=True, cleanup=True)
                return False, []
            elif res == "SUCCESS":
                #graph.edge(str(current_id), "DONE", tactic)
                #graph.render(f'logs/{proof_name}', view=False, quiet=True, cleanup=True)
                script.append(tactic)
                return True, script
            elif res == "PROVING":
                #update graph                  
                #for g in state["fg_goals"]:
                    #graph.node(str(g["id"]), str(g["type"]))
                    #graph.edge(str(current_id), str(g["id"]), tactic)
                script.append(tactic)
                local_envs = self.add_local_envs(local_envs, state)
             
        #graph.render(f'logs/{proof_name}', view=False, quiet=True, cleanup=True)
            
        print("Tried everyting...")
        return False, []
        
    def prove_single_local_env(self, proof_env, state, local_env, global_env, prev_tacs):
        tactic_probs = self.tacmodel.prove(local_env["goal"], local_env["local context"], global_env)
        topk, indices = torch.topk(input=tactic_probs, k=self.opts.num_tactics, dim=0, largest=True)
        tactic_queue = [self.tactics[index] for index in indices]
        index = 0

        while tactic_queue:
            tactic = tactic_queue.pop(index)
            if tactic in prev_tacs:
                continue
            state = proof_env.step(f"{tactic}.")
            res = state["result"]
            if res == "ERROR":
                continue
            if res == "MAX_NUM_TACTICS_REACHED":
                return "MAX", None, state
            if res == "SUCCESS":
                return "SUCCESS", tactic, state
                
            if res == "PROVING":
                # check if tactic was approved, but didn't drive the search forward
                goal_texts = [g["type"] for g in state["fg_goals"]]
                if local_env["goal"]["text"] in goal_texts:
                    #state = proof_env.step(f"Undo.")
                    continue
             
                return "PROVING", tactic, state
            
        return "FAILED", None, state
        
    
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
            local_env = {"goal": goal, "local context": local_context}
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


                
                
       
        
    
