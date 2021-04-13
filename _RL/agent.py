import torch, random, math
from datetime import datetime

from _RL.estimators.q import Q

import helpers

class ReplayMemory(object):
    def __init__(self):
        self.memory = []
        
    def push(self, pred, target, reward):
        self.memory.append((pred, target, reward))

    def sample(self, batch_size):
        return random.sample(self.memory, batch_size)

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

        ''' record valid search '''
        self.script = []

        ''' replay exprience used for training '''
        self.replay = ReplayMemory()

        ''' deep Q networks '''
        self.Q = Q(self.opts)
        self.target_Q = Q(self.opts) # added for more robust/stable training

        ''' environment and state '''
        self.proof_env = None
        self.state = None # triplet -> (goal, local context, global context)


    def reset(self, proof_env):
        self.num_steps = 0
        self.error_count = 0
        self.tot_reward = 0
        self.script = []

        self.replay.clear()
        self.proof_env = proof_env

        local_state = proof_env.init()
        goal, lc = helpers.process_local_env(local_state)
        gc = helpers.process_global_context(local_state)
        self.state = (goal, lc, gc)


    def update_state(self, local_state):
        gc = self.state[2]
        goal, lc = helpers.process_local_env(local_state)
        self.state = (goal, lc, gc)


    def update_target_Q(self):
        self.target_Q.load_state_dict(self.Q.state_dict())


    def make_action(self, action):
        prev_state = self.state
        local_state = self.proof_env.step(f'{action}.')
        result = local_state['result']
        if result == 'ERROR':
            self.state = prev_state
            self.error_count += 1
        else:
            print(result) # TODO: handle MAX here
            self.update_state(local_state)
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
            actions = helpers.get_actions(self.opts, self.state)
            action, q = self.eps_greedy_action(actions, q_values)


            ''' make action -> update state and get reward '''
            reward, result = self.make_action(action)
            self.tot_reward += reward


            ''' calc targets and update replay '''
            if result in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
                _q = -self.opts.reward
            elif result == 'SUCCESS':
                _q = self.opts.reward
            else:
                _q_values = self.target_Q(self.state)
                _q = max(_q_values)

            self.replay.push(q, _q, reward)
            

            ''' search is over '''
            if result in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED', 'SUCCESS']:
                valid_proof = True if result == 'SUCCESS' else False
                out = {
                    'res': valid_proof,
                    'replay': self.replay,
                    'script': self.script,
                    'error_count': self.error_count,
                    'rewards': self.tot_reward
                }
                return out
        
        return "This should never be reached..."


    def eps_greedy_action(self, actions, q_values):
        sample = random.random()
        eps_tresh = self.opts.epsilon_end + (self.opts.epsilon_start - self.opts.epsilon_end) \
                    * math.exp(-1. * self.num_steps / self.opts.epsilon_decay)
        self.num_steps += 1
        if  sample > eps_tresh:
            return self.best_action(actions, q_values)
        else:
            index = random.randint(0, len(actions)-1)
            q = q_values[index]
            action = actions[index]
            return action, q
    

    def best_action(self, actions, q_values):
        q = max(q_values)
        action = actions[torch.argmax(q_values)]
        return action, q


    def test(self, proof_env):
        pass