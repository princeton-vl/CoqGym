import torch, random, math
from datetime import datetime

from _RL.estimators.q import Q

import helpers

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
        self.tot_reward = 0
        self.legal_count = 0

        ''' record valid search '''
        self.script = []

        ''' replay exprience used for training '''
        self.replay = ReplayMemory(self.opts)

        ''' deep Q networks '''
        self.Q = Q(self.opts)
        self.target_Q = Q(self.opts) # added for more robust/stable training

        ''' environment and state '''
        self.proof_env = None
        self.state = None # triplet -> (goal, local context, global context)

        ''' greylist '''
        self.action_count = {}
        self.greylist = []
        


    def reset(self, proof_env):
        
        self.error_count = 0
        self.legal_count = 0
        self.tot_reward = 0

        self.script = []
        self.action_count = {}
        self.greylist = []

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

        self.action_count[action] = self.action_count.get(action, 0) + 1
        if self.action_count[action] > 5:
            self.greylist.append(action)

        if result not in ['SUCCESS', 'MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
            assert result != 'ERROR'
            assert not self.is_loop(prev_state, local_state)
            self.legal_count += 1
            self.update_state(prev_state, local_state)

        self.script.append(action)
        self.num_steps += 1

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
            actions = helpers.get_actions(self.opts, self.state)
            action, q, action_tensor = self.eps_greedy_action(actions, q_values)

            if action == "":
                valid_proof = False
                replay_stats = {self.opts.error_punishment: len([e for e in self.replay.memory if e[2] == self.opts.error_punishment]), 
                              self.opts.neutral_reward: len([e for e in self.replay.memory if e[2] == self.opts.neutral_reward]),
                              self.opts.success_reward: len([e for e in self.replay.memory if e[2] == self.opts.success_reward])}
                out = {
                    'res': valid_proof,
                    'legal_moves': self.legal_count,
                    'error_count': self.error_count,
                    'rewards': self.tot_reward,
                    'replay': (len(self.replay.memory), replay_stats),
                    'script': self.script
                }
                return out

            if not self.check_legality(action):
                continue

            ''' make action -> update state and get reward '''
            reward, result = self.make_action(action)
            self.tot_reward += reward


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
                    'legal_moves': self.legal_count,
                    'error_count': self.error_count,
                    'rewards': self.tot_reward,
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
            action = actions[index]
            action_tensor = torch.zeros(self.opts.action_space).to(self.opts.device)
            action_tensor[index] = 1
            return action, q, action_tensor
    

    def best_action(self, actions, q_values):
        q = max(q_values)
        index = torch.argmax(q_values)
        action = actions[index]

        top, indices = torch.topk(input=q_values, k=len(q_values), dim=0, largest=True)
        index_index = 0
        index = indices[index_index]
        q = top[index]
        action = actions[index]
        while not self.check_legality(action):
            index_index += 1
            self.error_count += 1
            if index_index >= len(indices):
                return "", None, None

            index = indices[index_index]
            q = top[index]
            action = actions[index]

        action_tensor = torch.zeros(self.opts.action_space).to(self.opts.device)
        action_tensor[index] = 1
        
        return action, q, action_tensor


    def check_legality(self, action):

        if action in self.greylist:
            return False

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


    def test(self, proof_env):
        res, script = self.prove_DFS(proof_env)
        return {"proved": res, "script": script}
        
    def prove_DFS(self, proof_env):
        self.reset(proof_env)
        node_ids = set() # keep track of all nodes seen so far
        root_id = helpers.state_id(self.state)
        node_ids.add(root_id)
        
        # initialize the stack
        stack = []
        stack.append(self.get_candidates())
        script = []

        
        # depth-first search starting from the trace
        while stack != [[]]:
            # pick a tactic
            if stack[-1] == []:  # all candidate have been tried, backtrack
                stack.pop()
                script.pop()
                local_state = self.proof_env.step("Undo.")
                self.update_state(self.state, local_state)
                continue
            else:
                tac = stack[-1].pop(0)
            if not self.check_legality(tac):
                self.proof_env.num_tactics_left -= 1
                continue
            
            _, result = self.make_action(tac)

            if result == "SUCCESS":            
                script.append(tac)
                return True, script
            elif result in ["MAX_NUM_TACTICS_REACHED", "MAX_TIME_REACHED"]:
                return False, script
            elif result in ["ERROR"]:
                continue
            else:                
                assert result == "PROVING"
                script.append(tac)
                sig = helpers.state_id(self.state)

                if sig in node_ids or len(script) >= self.opts.depth_limit:
                    local_state = self.proof_env.step("Undo.")
                    self.update_state(self.state, local_state)
                    script.pop()
                    continue

                node_ids.add(sig)
                stack.append(self.get_candidates())

        state = proof_env.step("Admitted.")
        return False, script

    def get_candidates(self):
        actions = helpers.get_actions(self.opts, self.state)
        q_values = self.Q(self.state)

        topk, indices = torch.topk(input=q_values, k=10, dim=0, largest=True)
        candidates = []
        for i in indices:
            candidates.append(actions[i])
        return candidates
