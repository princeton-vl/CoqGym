# Environment for interacting with Coq theorems during testing
from serapi import SerAPI, CoqExn, CoqTimeout
import re
from copy import deepcopy
from time import time
from collections import OrderedDict
import json
import sexpdata
from utils import update_env
from gallina import GallinaTermParser
import os
from glob import glob
import pdb


class ProofEnv:
    '''
    the interactive environment for proving a theorem
    should be created by FileEnv
    '''
    
    def __init__(self, proof, serapi, max_num_tactics, timeout):
        '''
        proof - the data structure for a proof in CoqGym
        serapi - the SerAPI at the beginning of the proof
        max_num_tactics - the maxium number of interactions for proving a theorem
        timeout - the maxium amount of time (in seconds) for each theorem 
        '''
        self.proof = proof
        self.serapi = serapi
        self.num_tactics_left = max_num_tactics
        self.timeout = timeout
        self.success = False
        self.failure = False


    def init(self):
        'return the initial goals and the global environment of the theorem'
        fg_goals, bg_goals, shelved_goals, given_up_goals = self.serapi.query_goals() 
        assert shelved_goals + given_up_goals == []
        self.start_time = time()
        return self.feedback('PROVING', env=self.proof['env'], fg_goals=fg_goals, bg_goals=bg_goals,
                                        shelved_goals=shelved_goals, given_up_goals=given_up_goals)


    def step(self, command):
        '''
        perform a single interaction
        the agent provides a command and get feedback from Coq
        valid commands include:
            tactics
            Admitted - to give up the proof
            Undo - to backtrack one step
            other valid Coq commands
        '''
        if self.success:
            return self.feedback('ALREADY_SUCCEEDED')
        if self.failure:
            return self.feedback('ALREADY_FAILED')
        time_left = self.timeout - (time() - self.start_time)
        print('%d: %s: %.02f' % (self.num_tactics_left, command, time_left))
        if time_left <= 0:
            return self.feedback('MAX_TIME_REACHED')

        self.serapi.push()  # save the state before executing the command
        try:
            ast = sexpdata.dumps(self.serapi.query_ast(command))
            if 'VernacExtend' in ast:  # is a tactic
                if self.num_tactics_left <= 0:
                    self.serapi.pop()
                    return self.feedback('MAX_NUM_TACTICS_REACHED')
                self.num_tactics_left -= 1
                command = 'timeout %d (%s).' % (time_left, command[:-1])
            responses, _ = self.serapi.execute(command)
            states_cnt = self.serapi.pull()  # delete the saved state if no error
        except CoqExn as ex: 
            self.serapi.pop()  # restore the state
            return self.feedback('ERROR', error=ex)
        except CoqTimeout as ex: 
            self.serapi.shutdown()
            return self.feedback('ERROR', error=ex)

        if '(VernacEndProof Admitted)' in ast:
            self.failure = True
            return self.feedback('GIVEN_UP')

        try:
            fg_goals, bg_goals, shelved_goals, given_up_goals = self.serapi.query_goals()
            time_left = self.timeout - (time() - self.start_time)
            if time_left < 0:
                return self.feedback('MAX_TIME_REACHED')
        except CoqTimeout as ex:
            self.serapi.shutdown()
            return self.feedback('ERROR', error=ex)

        if fg_goals + bg_goals + shelved_goals + given_up_goals == []:  # no goals left
            self.success = True
            return self.feedback('SUCCESS')
        elif shelved_goals + given_up_goals != []:
            self.serapi.pop_n(states_cnt)
            return self.feedback('ERROR', error=(shelved_goals, given_up_goals))
        else:
            return self.feedback('PROVING', fg_goals=fg_goals, bg_goals=bg_goals, 
                                            shelved_goals=shelved_goals, given_up_goals=given_up_goals)


    def feedback(self, result, **kwargs):
        obs = {'result': result, 'num_tactics_left': self.num_tactics_left, 'time_left': self.timeout - (time() - self.start_time)}
        for k, v in kwargs.items():
            obs[k] = v
        return obs


class FileEnv:
    '''
    a generator of the theorems in a Coq file
    the agent iterate through them and interact with each theorem sequentially
    '''

    def __init__(self, filename, max_num_tactics, timeout, with_hammer=None, hammer_timeout=None):
        '''
        filename - the json file in CoqGym
        max_num_tactics - the maxium number of interactions for proving a theorem
        timeout - the maxium amount of time (in seconds) for each theorem
        '''
        file_data = json.load(open(filename))
        self.vernac_cmds = [cmd[:2] for cmd in file_data['vernac_cmds']]
        self.proofs = file_data['proofs']
        self.max_num_tactics = max_num_tactics
        self.timeout = timeout
        self.with_hammer = with_hammer
        self.hammer_timeout = hammer_timeout
        self.serapi = self.initialize_serapi()


    def initialize_serapi(self):
        serapi = SerAPI(timeout=1200)
        if self.with_hammer is not None:
            atp_limit = 29 * self.hammer_timeout // 60
            reconstr_limit = 28 * self.hammer_timeout // 60
            crush_limit = 3 * self.hammer_timeout // 60
            serapi.execute('From Hammer Require Import Hammer. Set Hammer ATPLimit %d. Set Hammer ReconstrLimit %d. Set Hammer CrushLimit %d.' % (atp_limit, reconstr_limit, crush_limit))
            if self.with_hammer == 'Z3':
                serapi.execute('Unset Hammer Vampire. Unset Hammer Eprover. Unset Hammer CVC4.')
            elif self.with_hammer == 'Vampire':
                serapi.execute('Unset Hammer Z3. Unset Hammer Eprover. Unset Hammer CVC4.')
            elif self.with_hammer == 'Eprover':
                serapi.execute('Unset Hammer Z3. Unset Hammer Vampire. Unset Hammer CVC4.')
            elif self.with_hammer == 'CVC4':
                serapi.execute('Unset Hammer Z3. Unset Hammer Vampire. Unset Hammer Eprover.')
            else:
                assert self.with_hammer == 'All'
        return serapi


    def __iter__(self):
        self.cmd_idx = 0
        self.next_proof_idx = 0
        self.env = {'constants': [], 'inductives': []}
        return self
 

    def __next__(self):
        if self.next_proof_idx >= len(self.proofs):  # no more theorem
            raise StopIteration

        next_proof = self.proofs[self.next_proof_idx]
        self.env = update_env(self.env, next_proof['env_delta'])
        del next_proof['env_delta']
        next_proof['env'] = self.env

        if self.serapi.dead:
            self.serapi = self.initialize_serapi()
            self.cmd_idx = 0
        elif self.next_proof_idx > 0:  # rollback to the start of the current proof
            self.serapi.pop()

        if self.next_proof_idx > 0 and self.next_proof_idx % 30 == 0:  # renew the SerAPI to prevent stack overflow
            self.serapi.clean()
            self.serapi = self.initialize_serapi()
            self.cmd_idx = 0

        while self.cmd_idx <= next_proof['line_nb']:
            cmd, _ = self.vernac_cmds[self.cmd_idx]
            self.serapi.execute(cmd)
            self.cmd_idx += 1

        self.serapi.push()
       
        self.next_proof_idx += 1
        return ProofEnv(next_proof, self.serapi, self.max_num_tactics, self.timeout)


    def __len__(self):
        return len(self.proofs)
 

    def test(self):
        assert self.cmd_idx is None
        self.serapi.push()
        for cmd, _ in self.vernac_cmds:
            self.serapi.execute(cmd)
        self.serapi.pop()
       

    def __enter__(self):
        return self


    def __exit__(self, exc_type, exc_value, traceback):
        self.serapi.clean()


if __name__ == '__main__':
    f = 'data/StructTact/Assoc.json'
    print(f)
    with FileEnv(f, max_num_tactics=100, timeout=600) as file_env:
        for proof_env in file_env:
            print(proof_env.proof['name'])
            proof_env.init()
            print(proof_env.step('Admitted.'))
