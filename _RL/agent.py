import torch, random, math
from datetime import datetime

from _RL.estimators.sarsa import SARSA

import helpers


class Agent:
    def __init__(self, opts):
        self.opts = opts
        self.q_function = SARSA(self.opts)
        self.steps_done = 0


    def train(self, proof_env):
        if not self.q_function.training:
            self.q_function.train()

        state_actions = []
        eligibilities = {}
        
        state = proof_env.init()
        gc = helpers.process_global_context(state)
    
        script = []
        error_action_count = 0
        tot_reward = 0

        while True:
            
            ''' get Q value and policy action for current state '''
            state_id = helpers.state_id(state)
            q_values, actions = self.q_function(state, gc), helpers.get_actions(self.opts, state, gc)
            action, q = self.pick_action(actions, q_values)
            if len(state_actions) > 10:
                state_actions.pop(0)            
            state_actions.append((state_id, action))

            ''' make action, get reward '''
            prev_state = state
            state = proof_env.step(f'{action}.')
            r = helpers.get_reward(self.opts, state)
            tot_reward += r
            if state['result'] == 'ERROR':
                state = prev_state
                error_action_count += 1
            else:
                script.append(action)

            ''' calc temporal difference '''
            if state['result'] in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
                next_q = -self.opts.reward
            elif state['result'] == 'SUCCESS':
                next_q = self.opts.reward
            else:
                next_q_values, next_actions = self.q_function(state, gc), helpers.get_actions(self.opts, state, gc)
                next_action, next_q = self.pick_best_action(next_actions, next_q_values)
            #print(q)
            #print(next_q)
            td = r + self.opts.discount*next_q - q
            #print(td)

            '''  set eligibility '''
            eligibilities[(state_id, action)] = 1

            ''' update network '''
            for sap in state_actions:
                # Q(s,a) <- Q(s,a) + α*δ*e(s,a)
                with torch.no_grad():
                    for p in self.q_function.parameters():
                        # wi ← wi +α*δ*e(s, a)
                        new_val = p + self.opts.lr*td*eligibilities[sap]
                        p.copy_(new_val)                        
                # e(s,a) <- γ*λ*e(s,a)
                eligibilities[sap] = self.opts.discount*self.opts.eligibility*eligibilities[sap]

            
            ''' search is over '''
            if state['result'] in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
                return {'res': False, 'script': script, 'error_count': error_action_count, 'rewards': tot_reward}
            elif state['result'] == 'SUCCESS':
                return {'res': True, 'script': script, 'error_count': error_action_count, 'rewards': tot_reward}
        
        return "This should never be reached..."

    def pick_action(self, actions, q_values):
        sample = random.random()
        eps_tresh = self.opts.epsilon_end + (self.opts.epsilon_start - self.opts.epsilon_end) \
                    * math.exp(-1. * self.steps_done / self.opts.epsilon_decay)
        self.steps_done += 1
        #print(eps_tresh)
        if  sample > eps_tresh:
            return self.pick_best_action(actions, q_values)
        else:
            index = random.randint(0, len(actions)-1)
            q = q_values[index]
            action = actions[index]
            return action, q
    
    def pick_best_action(self, actions, q_values):
        q = max(q_values)
        action = actions[torch.argmax(q_values)]
        return action, q

    def test(self, proof_env):
        pass