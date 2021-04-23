

class Agent:
    def __init__(self, opts, model):
        self.opts = opts
        self.script = []
        self.model = model

        ''' environment and state '''
        self.proof_env = None
        self.state = None # triplet -> (goal, local context, global context)        


    def reset(self, proof_env):
        self.script = []
        self.proof_env = proof_env

        local_state = proof_env.init()
        goal, lc = helpers.process_local_env(local_state)
        gc = helpers.process_global_context(local_state)
        self.state = (goal, lc, gc)


    def update_state(self, prev_state, local_state):
        gc = self.state[2]
        goal, lc = helpers.process_local_env(local_state)
        self.state = (goal, lc, gc)


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