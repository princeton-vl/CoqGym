import torch, random, math, json
from datetime import datetime

from _RL.nn_model.q import Q
from _SL.nn_model.gast_lc import GastLC
from _SL.nn_model.gast_gc import GastGC

import _RL.helpers as helpers

class ReplayMemory(object):
    def __init__(self, opts):
        '''
        Training examples, based on the temporal difference.
        That is,    target -> reward + dicount*target_Q(s', a'), where a' is the best action in that state according to target_Q.
                    prediction -> Q(s, a), where you allow a to be choosen in an eps-greedy manner.
        -> memory contains quadruples ( Q(s, a), target_Q(s', a'), reward ) 
        '''
        self.opts = opts
        self.memory = []
        
    def push(self, pred, target, reward):
        if reward == 1.0:
            self.memory.append((pred, target, reward))
        elif len(self.memory) < 256:
            self.memory.append((pred, target, reward))
        
    def sample(self, batch_size):
        res = []
        for example in self.memory:
            if example[2] == self.opts.success_reward:
                res.append(example)
        randoms = random.sample(self.memory, batch_size-len(res))
        return res+randoms

    def clear(self):
        self.memory = []

    def __len__(self):
        return len(self.memory)

class Agent:
    def __init__(self, opts):
        self.opts = opts

        ''' statistics '''
        self.num_steps = 0
        self.error_count = 0

        ''' record valid search '''
        self.script = []

        ''' replay exprience used for training '''
        self.replay = ReplayMemory(self.opts)

        ''' deep Q networks '''
        tacmodel_path = "../_SL/models/best/acc/synthetic/gast_tac.pth"
        if opts.device.type == "cpu":
            taccheck = torch.load(tacmodel_path, map_location="cpu")
        else:
            taccheck = torch.load(tacmodel_path)
        self.Q = Q(self.opts)
        self.target_Q = Q(self.opts) # added for more robust/stable training
        self.Q.load_state_dict(taccheck["state_dict"])
        self.target_Q.load_state_dict(taccheck["state_dict"])
        self.Q.to(opts.device)
        self.target_Q.to(opts.device)

        ''' environment and state '''
        self.proof_env = None
        self.state = None # triplet -> (goal, local context, global context)

        with open(self.opts.tactics) as f:  self.tactics = json.load(f)

        lcmodel_path = "../_SL/models/best/acc/human/gast_lc.pth"
        gcmodel_path = "../_SL/models/best/acc/synthetic/gast_gc.pth"
        self.lcmodel = GastLC(opts)
        self.gcmodel = GastGC(opts)
        if opts.device.type == "cpu":
            lccheck = torch.load(lcmodel_path, map_location="cpu")
            gccheck = torch.load(gcmodel_path, map_location="cpu")
        else:
            lccheck = torch.load(lcmodel_path)
            gccheck = torch.load(gcmodel_path)
        self.lcmodel.load_state_dict(lccheck["state_dict"])
        self.gcmodel.load_state_dict(gccheck["state_dict"])
        self.lcmodel.to(opts.device)
        self.gcmodel.to(opts.device)
        self.lcmodel.eval()
        self.gcmodel.eval()
        


    def reset(self, proof_env):
        
        self.error_count = 0

        self.script = []

        self.proof_env = proof_env

        local_state = proof_env.init()
        goal, lc = helpers.process_local_env(local_state)
        gc = helpers.process_global_context(local_state)
        self.state = (goal, lc, gc)

    def update_target_Q(self):
        self.target_Q.load_state_dict(self.Q.state_dict())


    def update_state(self, prev_state, local_state):
        gc = self.state[2]
        goal, lc = helpers.process_local_env(local_state)
        self.state = (goal, lc, gc)


    def make_action(self, action):
        prev_state = self.state
        local_state = self.proof_env.step(f'{action}.')
        result = local_state['result']

        if result not in ['SUCCESS', 'MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
            assert result != 'ERROR'
            assert not self.is_loop(prev_state, local_state)
            self.update_state(prev_state, local_state)

        self.script.append(action)

        reward = helpers.get_reward(self.opts, result)
        return reward, result


    def train(self, proof_env):
        if not self.Q.training: self.Q.train()
        if not self.target_Q.training: self.target_Q.train()
        
        ''' get ready for new proof search '''
        self.reset(proof_env)

        ''' begin search '''
        while True:
            ''' get Q value and eps-greedy action for current state '''
            q_values = self.Q(self.state)
            actions = self.tactics
            action, q = self.eps_greedy_action(actions, q_values)

            if action == "":
                valid_proof = False
                replay_stats = {self.opts.error_punishment: len([e for e in self.replay.memory if e[2] == self.opts.error_punishment]), 
                              self.opts.neutral_reward: len([e for e in self.replay.memory if e[2] == self.opts.neutral_reward]),
                              self.opts.success_reward: len([e for e in self.replay.memory if e[2] == self.opts.success_reward])}
                out = {
                    'res': valid_proof,
                    'error_count': self.error_count,
                    'replay': (len(self.replay.memory), replay_stats),
                    'script': self.script
                }
                return out
            
            if not self.check_legality(action):
                continue

            ''' make action -> update state and get reward '''
            reward, result = self.make_action(action)
            
            ''' calc targets and update replay '''
            if result in ['PROVING']:
                _q_values = self.target_Q(self.state)
                _q = max(_q_values)
            else:
                _q = 0

            self.replay.push(q, _q, reward)
            

            ''' search is over '''
            if result in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED', 'SUCCESS']:
                valid_proof = True if result == 'SUCCESS' else False
                replay_stats = {self.opts.error_punishment: len([e for e in self.replay.memory if e[2] == self.opts.error_punishment]), 
                              self.opts.neutral_reward: len([e for e in self.replay.memory if e[2] == self.opts.neutral_reward]),
                              self.opts.success_reward: len([e for e in self.replay.memory if e[2] == self.opts.success_reward])}
                out = {
                    'res': valid_proof,
                    'error_count': self.error_count,
                    'replay': (len(self.replay.memory), replay_stats),
                    'script': self.script
                }
                return out
        
        return "This should never be reached..."


    def get_eps_tresh(self):
        return self.opts.epsilon_end + (self.opts.epsilon_start - self.opts.epsilon_end) \
                    * math.exp(-1. * self.num_steps / self.opts.epsilon_decay)

    def eps_greedy_action(self, actions, q_values):
        sample = random.random()
        eps_tresh = self.get_eps_tresh()
        
        if  sample > eps_tresh:
            return self.best_action(actions, q_values)
        else:
            index = random.randint(0, len(actions)-1)
            q = q_values[index]
            tac = actions[index]
            arg_probs = self.get_arg_probs(self.state[0], self.state[1], self.state[2])
            action = self.prep_tac(tac, arg_probs)
            return action, q

    def best_action(self, actions, q_values):
        top, indices = torch.topk(input=q_values, k=len(q_values), dim=0, largest=True)
        index_index = 0
        index = indices[index_index]
        q = top[index]
        tac = actions[index]
        arg_probs = self.get_arg_probs(self.state[0], self.state[1], self.state[2])
        action = self.prep_tac(tac, arg_probs)
        while not self.check_legality(action):
            index_index += 1
            self.error_count += 1
            if index_index >= len(indices):
                return "", None, None

            index = indices[index_index]
            q = top[index]
            action = actions[index]
        
        return action, q


    def check_legality(self, action):

        response = self.proof_env.step(f'{action}.')
        self.proof_env.step(f'Undo.')

        self.proof_env.num_tactics_left += 2
        
        res = response['result']

        if res in ['ERROR']:
            return False
        elif res in ['SUCCESS', 'MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
            return True

        return not self.is_loop(self.state, response)


    def is_loop(self, prev_state, new_local):
        gc = self.state[2]
        goal, lc = helpers.process_local_env(new_local)
        new_state = (goal, lc, gc)
        old_id = helpers.state_id(prev_state)
        new_id = helpers.state_id(new_state)
        return old_id == new_id


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
