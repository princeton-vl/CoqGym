# Python class for interacting with SerAPI
# Used to extract proofs in the dataset and to prove theorems during testing
import os
import sys
from re_patterns import *
import pexpect
from pexpect.popen_spawn import PopenSpawn
import signal
from itertools import chain
import sexpdata
from sexpdata import Symbol
from utils import normalize_spaces, log
import pdb


class CoqExn(Exception):

    def __init__(self, err_msg, full_sexp):
        super().__init__()
        self.err_msg = err_msg
        self.full_sexp = full_sexp

    def __str__(self):
        return self.err_msg


    def __repr__(self):
        return str(self)


class CoqTimeout(Exception):
    pass


def escape(vernac_cmd):
    return vernac_cmd.replace('\\', '\\\\').replace('"', '\\"')


def symbol2str(s):
    return s.value() if isinstance(s, Symbol) else str(s)


def print_mod_path(modpath):
    if modpath[0] == Symbol('MPdot'):
        return print_mod_path(modpath[1]) + '.' + symbol2str(modpath[2][1])
    elif modpath[0] == Symbol('MPfile'):
        return '.'.join([symbol2str(x[1]) for x in modpath[1][1]][::-1])
    else: 
        assert modpath[0] == Symbol('MPbound')
        return '.'.join([symbol2str(x[1]) for x in modpath[1][2][1]][::-1] + [symbol2str(modpath[1][1][1])])


def mod_path_file(modpath):
    if modpath[0] == Symbol('MPdot'):
        return mod_path_file(modpath[1])
    elif modpath[0] == Symbol('MPfile'):
        return '.'.join([symbol2str(x[1]) for x in modpath[1][1]][::-1])
    else:
        assert modpath[0] == Symbol('MPbound')
        return ''


class SerAPI:

    def __init__(self, timeout, debug=False):
        'Initialize the SerAPI subprocess'
        self.debug = debug
        try:
            self.proc = PopenSpawn('sertop --implicit --omit_loc --print0', encoding='utf-8', timeout=timeout, maxread=10000000)
        except FileNotFoundError:
            log('Please make sure the "sertop" program is in the PATH.\nYou may have to run "eval $(opam env)".', 'ERROR')
            sys.exit(1)
        self.proc.expect_exact('(Feedback((doc_id 0)(span_id 1)(route 0)(contents Processed)))\0')
        self.send('Noop')
        self.states_stack = []

        # global printing options
        self.execute('Unset Printing Notations.')
        self.execute('Unset Printing Wildcard.')
        self.execute('Set Printing Coercions.')
        self.execute('Unset Printing Allow Match Default Clause.')
        self.execute('Unset Printing Factorizable Match Patterns.')
        self.execute('Unset Printing Compact Contexts.')
        self.execute('Set Printing Implicit.')
        self.execute('Set Printing Depth 999999.')
        self.execute('Unset Printing Records.')

        # initialize the state stack
        self.push()
  
        self.ast_cache = {}
        self.dead = False


    def set_timeout(self, timeout):
        self.proc.timeout = timeout


    def get_timeout(self):
        return proc.timeout


    def send(self, cmd):
        'Send a command to SerAPI and retrieve the responses'
        #print(cmd)
        assert '\n' not in cmd
        self.proc.sendline(cmd)
        try:
            self.proc.expect(['\(Answer \d+ Ack\)\x00.*\(Answer \d+ Completed\)\x00',
                              '\(Answer \d+ Ack\)\x00.*\(Answer \d+\(CoqExn.*\)\x00'])
        except pexpect.TIMEOUT as ex:
            print(self.proc.before)
            raise CoqTimeout
        raw_responses = self.proc.after
        #print(raw_responses)
        ack_num = int(re.search(r'^\(Answer (?P<num>\d+)', raw_responses)['num'])
        for num in re.findall(r'(?<=\(Answer) \d+', raw_responses):
            assert int(num) == ack_num
        responses = []
        msg_str = []
        for item in raw_responses.split('\x00'):
            item = item.strip()
            if item == '':
                continue
            if not item.startswith('(Feedback') and not item.startswith('(Answer'):
                m = re.search(r'\(Feedback|\(Answer', item)
                if m is None:
                    continue
                item = item[m.span()[0]:]
                assert item.endswith(')')
            parsed_item = sexpdata.loads(item, nil=None, true=None)
            if 'CoqExn' in item:  # an error occured in Coq
                assert parsed_item[2][0] == Symbol('CoqExn')
                raise CoqExn(sexpdata.dumps(parsed_item[2][4]), sexpdata.dumps(parsed_item[2]))
            if item.startswith('(Feedback'):  # ignore Feedback for now
                try:
                   msg = parsed_item[1][3][1]
                   if isinstance(msg, list) and msg != [] and msg[0] == Symbol('Message'):
                       msg_sexp, _ = self.send('(Print ((pp_format PpStr)) (CoqPp %s))' % sexpdata.dumps(msg[3]))
                       msg_str.extend([symbol2str(x[1]) for x in msg_sexp[1][2][1]])
                except IndexError:
                    pass
                continue
            responses.append(parsed_item)
        msg_str = '\n'.join(msg_str)
        return responses, raw_responses


    def send_add(self, cmd, return_ast):
        'Send a (Add () "XXX") command to SerAPI, return the state id and optionally the AST'
        responses, raw_responses = self.send('(Add () "%s")' % escape(cmd))
        state_ids = [int(sid) for sid in ADDED_STATE_PATTERN.findall(raw_responses)]
        state_id = state_ids[-1]
        if self.states_stack != []:
            self.states_stack[-1].append(state_id)
        if return_ast:
            if cmd not in self.ast_cache:
                self.ast_cache[cmd] = self.query_ast(cmd)
            ast = self.ast_cache[cmd]
        else:
            ast = None
        return state_id, ast


    def query_ast(self, cmd):
        'Query the AST of the vernac command just added'
        responses, _ = self.send('(Parse () "%s")' % escape(cmd))
        ast = responses[1][2][1][0]
        assert ast[0] == Symbol('CoqAst')
        return ast


    def query_library(self, lib):
        responses, _ = self.send('(Query () (LocateLibrary "%s"))' % lib)
        physical_path = symbol2str(responses[1][2][1][0][3])
        return physical_path


    def query_qualid(self, qualid):
        responses, _ = self.send('(Query () (Locate "%s"))' % qualid)
        if responses[1][2][1] == [] and qualid.startswith('SerTop.'):
            qualid = qualid[len('SerTop.'):]
            responses, _ = self.send('(Query () (Locate "%s"))' % qualid)
        assert len(responses[1][2][1]) == 1
        short_responses = responses[1][2][1][0][1][0][1]
        assert short_responses[1][0] == Symbol('DirPath')
        short_ident = '.'.join([symbol2str(x[1]) for x in short_responses[1][1][::-1]] + [symbol2str(short_responses[2][1])])
        return short_ident


    def query_env(self, current_file):
        'Query the global environment'
        responses, _ = self.send('(Query () Env)')
        env = responses[1][2][1][0]

        # store the constants
        constants = []
        for const in env[1][0][1][0][1]:
            # identifier
            qualid = print_mod_path(const[0][1]) + '.' + \
                '.'.join([symbol2str(x[1]) for x in const[0][2][1][::-1]] + [symbol2str(const[0][3][1])])
            if qualid.startswith('SerTop.'):
                logical_path = 'SerTop'
                physical_path = current_file
            else:
                logical_path = mod_path_file(const[0][1])
                assert qualid.startswith(logical_path)
                physical_path = os.path.relpath(self.query_library(logical_path))
            physical_path += ':' + qualid[len(logical_path) + 1:]
            short_ident = self.query_qualid(qualid)
            # term
            assert const[1][0][1][0] == Symbol('const_body')
            if const[1][0][1][1][0] == Symbol('Undef'):  # delaration
                opaque = None
                term = None
            elif const[1][0][1][1][0] == Symbol('Def'):  # transparent definition
                opaque = False
                term = None
            else:
                assert const[1][0][1][1][0] == Symbol('OpaqueDef')  # opaque definition
                opaque = True
                term = None
            # type
            assert const[1][0][2][0] == Symbol('const_type')
            type_sexp = sexpdata.dumps(const[1][0][2][1])
            type = self.print_constr(type_sexp)
            sort = self.query_type(type_sexp, return_str=True)
            constants.append({'physical_path': physical_path, 'short_ident': short_ident, 'qualid': qualid, 'term': term, 
                              'type': type, 'sort': sort, 'opaque': opaque, 'sexp': sexpdata.dumps(const[1][0][2][1])})

        # store the inductives
        inductives = []
        for induct in env[1][0][1][1][1]:
            # identifier
            qualid = print_mod_path(induct[0][1]) + '.' + \
                '.'.join([symbol2str(x[1]) for x in induct[0][2][1][::-1]] + [symbol2str(induct[0][3][1])])
            short_ident = self.query_qualid(qualid)
            if qualid.startswith('SerTop.'):
                logical_path = 'SerTop'
                physical_path = current_file
            else:
                logical_path = mod_path_file(induct[0][1])
                physical_path = os.path.relpath(self.query_library(logical_path))
            assert qualid.startswith(logical_path)
            physical_path += ':' + qualid[len(logical_path) + 1:]
            # blocks
            blocks = []
            for blk in induct[1][0][0][1]:
                blk_qualid = '.'.join(qualid.split('.')[:-1] + [symbol2str(blk[0][1][1])])
                blk_short_ident = self.query_qualid(blk_qualid)
                # constructors
                constructors = []
                for c_name, c_type in zip(blk[3][1], blk[4][1]):
                    c_name = symbol2str(c_name[1])
                    c_type = self.print_constr(sexpdata.dumps(c_type))
                    #if c_type is not None:
                    #    c_type = UNBOUND_REL_PATTERN.sub(short_ident, c_type)
                    constructors.append((c_name, c_type))
                blocks.append({'short_ident': blk_short_ident, 'qualid': blk_qualid, 'constructors': constructors})

            inductives.append({'physical_path': physical_path, 'blocks': blocks, 'is_record': induct[1][0][1][1] != Symbol('NotRecord'), 'sexp': sexpdata.dumps(induct)})

        return constants, inductives


    def query_goals(self):
        'Retrieve a list of open goals'
        responses, _ = self.send('(Query () Goals)')
        assert responses[1][2][0] == Symbol('ObjList')
        if responses[1][2][1] == []:  #  no goals
            return [], [], [], []
        else:
            assert len(responses[1][2][1]) == 1
            def store_goals(goals_sexp):
                goals = []
                for g in goals_sexp:
                    hypotheses = []
                    for h in g[2][1]:
                        h_sexp = sexpdata.dumps(h[2])
                        hypotheses.append({'idents': [symbol2str(ident[1]) for ident in h[0][::-1]], 
                                           'term': [None if t == [] else self.print_constr(sexpdata.dumps(t)) for t in h[1]],
                                           'type': self.print_constr(h_sexp),
                                           'sexp': h_sexp}) 
                    
                    type_sexp = sexpdata.dumps(g[1][1])
                    goals.append({'id': int(g[0][1]),
                                  'type': self.print_constr(type_sexp),
                                  'sexp': type_sexp,
                                  'hypotheses': hypotheses[::-1]})
                return goals
            fg_goals = store_goals(responses[1][2][1][0][1][0][1])
            bg_goals = store_goals(list(chain.from_iterable(chain.from_iterable(responses[1][2][1][0][1][1][1]))))
            shelved_goals = store_goals(responses[1][2][1][0][1][2][1])
            given_up_goals = store_goals(responses[1][2][1][0][1][3][1])
            return fg_goals, bg_goals, shelved_goals, given_up_goals


    def has_open_goals(self):
        responses, _ = self.send('(Query () Goals)')
        assert responses[1][2][0] == Symbol('ObjList')
        return responses[1][2][1] != []


    def print_constr(self, sexp_str):
        if not hasattr(self, 'constr_cache'):
            self.constr_cache = {}
        if sexp_str not in self.constr_cache:
            try:
                responses, _ = self.send('(Print ((pp_format PpStr)) (CoqConstr %s))' % sexp_str)
                self.constr_cache[sexp_str] = normalize_spaces(symbol2str(responses[1][2][1][0][1]))
            except CoqExn as ex:
                if ex.err_msg == 'Not_found':
                    return None
                else:
                    raise ex
            except TypeError as ex:
                self.constr_cache[sexp_str] = normalize_spaces(symbol2str(responses[0][2][1][0][1]))
        return self.constr_cache[sexp_str]


    def query_vernac(self, cmd):
        return self.send('(Query () (Vernac "%s"))' % escape(cmd))


    def query_type(self, term_sexp, return_str=False):
        try:
            responses, _ = self.send('(Query () (Type %s))' % term_sexp)
        except CoqExn as ex:
            if ex.err_msg == 'Not_found':
                return None
            else:
                raise ex
        assert responses[1][2][1][0][0] == Symbol('CoqConstr')
        type_sexp = responses[1][2][1][0][1]
        if return_str:
            return self.print_constr(sexpdata.dumps(type_sexp))
        else:
            return type_sexp


    def execute(self, cmd, return_ast=False):
        'Execute a vernac command'
        state_id, ast = self.send_add(cmd, return_ast)
        responses, _ = self.send('(Exec %d)' % state_id)
        return responses, sexpdata.dumps(ast)


    def push(self):
        'push a new frame on the state stack (a checkpoint), which can be used to roll back to the current state'
        self.states_stack.append([])


    def cancel(self, states):
        self.send('(Cancel (%s))' % ' '.join([str(s) for s in states]))


    def pull(self):
        'remove a checkpoint created by push'
        states = self.states_stack.pop()
        self.states_stack[-1].extend(states)
        return len(states)


    def pop(self):
        'rollback to a checkpoint created by push'
        self.cancel(self.states_stack.pop())


    def pop_n(self, cnt):
        states = []
        for i in range(cnt):
            states.append(self.states_stack[-1].pop())
        self.cancel(states)


    def clean(self):
        self.proc.sendeof()
        self.proc.wait()
        self.dead = True

    def shutdown(self):
        self.proc.kill(signal.SIGKILL)
        self.dead = True

    def __enter__(self):
        return self


    def __exit__(self, exc_type, exc_value, traceback):
        self.clean()


if __name__ == '__main__':
    import random
    random.seed(1)
    with SerAPI() as serapi:
        serapi.execute('Require Import Coq.Program.Basics.')
        serapi.execute('Locate "_ ∘ _".')
