import os, logging, json, torch, pickle, random
from glob import glob
from utils import SexpCache
from gallina import GallinaTermParser, traverse_postorder
from hashlib import sha1
from torch_geometric.data import Data, Batch
from torch.utils.data import Dataset
from lark import Tree


class ProofStepData(Dataset):
    def __init__(self, opts, split):
        super().__init__()
        self.opts = opts
        self.split = split
        self.datapath = self.opts.proof_steps
        self.filepath = f"{self.datapath}/{self.split}"
        self.files = os.listdir(self.filepath)
        for i, file_name in enumerate(self.files):
            self.files[i] = f"{self.filepath}/{file_name}"
        random.shuffle(self.files)
        self.size = len(self.files)

    def __len__(self):
        return self.size
    
    def __getitem__(self, idx):
        return pickle.load(open(self.files[idx], "rb"))


def merge(batch):
        fields = [
            "file",
            "proof_name",
            "n_step",
            "env",
            "local_context",
            "goal",
            "is_synthetic",
            "tactic",
        ]
        data_batch = {key: [] for key in fields}
        for example in batch:
            for key, value in example.items():
                if key not in fields:
                    continue
                data_batch[key].append(value)
        return data_batch


def files_on_split(opts):
    root = opts.data
    with open(opts.split) as f: split = json.load(f)

    train_files, valid_files, test_files = [], [], []
    
    for proj in split['projs_train']:
        train_files.extend(glob(os.path.join(root, f'{proj}/**/*.json'), recursive=True))
        
    for proj in split['projs_valid']:
        valid_files.extend(glob(os.path.join(root, f'{proj}/**/*.json'), recursive=True))
        
    for proj in split['projs_test']:
        test_files.extend(glob(os.path.join(root, f'{proj}/**/*.json'), recursive=True))
    
    return train_files, valid_files, test_files

def setup_loggers(opts):
    try:
        os.remove(opts.run)
        os.remove(opts.res)
    except:
        pass
                        
    run_handler = logging.FileHandler(opts.run)
    res_handler = logging.FileHandler(opts.res)
    
    run_handler.setFormatter(logging.Formatter('%(asctime)s:\t%(message)s'))
    res_handler.setFormatter(logging.Formatter('%(asctime)s:\t%(message)s'))
    
    run_logger = logging.getLogger('run log')
    res_logger = logging.getLogger('test log')
    
    run_logger.addHandler(run_handler)
    res_logger.addHandler(res_handler)
    
    run_logger.setLevel(logging.INFO)
    res_logger.setLevel(logging.INFO)
    
    run_logger.propagate = False
    res_logger.propagate = False
    
    return run_logger, res_logger


sexp_cache = SexpCache('../sexp_cache', readonly=True)
term_parser = GallinaTermParser(caching=True)

def get_actions(opts, state):
    goal, lc, gc = state[0], state[1], state[2]        
    with open(opts.tactics_sorted) as f: tactics_sorted = json.load(f)
    non_args = tactics_sorted['non_args']
    gc_args = tactics_sorted['gc_args']
    lc_args = tactics_sorted['lc_args']

    res = []
    for tactic in non_args:
        tmp = prep_tac(tactic, lc, gc)
        res += tmp
    for tactic in lc_args:
        tmp = prep_tac(tactic, lc, gc)
        res += tmp
    for tactic in gc_args:
        tmp = prep_tac(tactic, lc, gc)
        res += tmp

    assert len(res) == opts.action_space
    return res

def process_local_env(state):
    goals = []
    local_contexts = []
    for g in state['fg_goals']:
        goal = {'id': g['id'], 'text': g['type'], 'ast': term_parser.parse(g['sexp']), 'sexp': g['sexp']}
        local_context = []
        for i, h in enumerate(g['hypotheses']):
            for ident in h['idents']:
                local_context.append({'ident': ident, 'text': h['type'], 'ast': term_parser.parse(h['sexp']), 'sexp': h['sexp']})

        goals.append(goal)
        local_contexts.append(local_context)
    
    for i, lc in enumerate(local_contexts):
        local_contexts[i] = padd_context(lc)

    return goals[0], local_contexts[0]

def process_global_context(state):
    global_context = []
    toplevel_consts = [const for const in state['env']['constants'] if const['qualid'].startswith('SerTop')]

    for const in toplevel_consts[-10:]:
        ast = sexp_cache[const['sexp']]
        global_context.append({'ident': const['qualid'], 'text': const['type'], 'ast': term_parser.parse(ast), 'sexp': const['sexp']})
    
    return padd_context(global_context)

def padd_context(c):
    if len(c) > 10:
        return c[0:10]
        
    while len(c) < 10:
        empty = {'ident': '', 'text': '', 'ast': Tree(data=None, children=None), 'sexp': ''}
        c.append(empty)

    return c

def prep_tac(tactic, lc, gc):
    res = []
    
    '''
    # specialize
    if tactic == 'specialize':
        for c1 in lc:
            lc_arg = c1['ident']
            for c2 in gc:
                gc_arg = c2['qualid']
                res.append(f'specialize ({lc_arg} {gc_arg})')
    '''

    # froced theorem
    if tactic in ['apply', 'rewrite', 'unfold', 'destruct', 'elim', 'case', 'generalize', 'exact']:
        i = 0
        while len(res) < 10:
            if i < len(gc):
                res.append(f"{tactic} {gc[i]['ident']}")
            else:
                res.append(f"{tactic} NONE")
            i += 1            

    # forced assumption
    elif tactic in ['induction', 'exists', 'revert', 'inversion_clear', 'injection', 'contradict']:
        i = 0
        while len(res) < 10:
            if i < len(lc):
                res.append(f"{tactic} {lc[i]['ident']}")
            else:
                res.append(f"{tactic} NONE")
            i += 1
    else:
        res.append(tactic)
    
    return res

def prep_ast(opts, ast):
    with open(opts.nonterminals) as f: nonterminals = json.load(f)
    edge_index = create_edge_index(ast)
    x = one_hot_encode(ast, nonterminals)
    
    graph_list = [Data(x=x, edge_index=edge_index)]
    batch = Batch().from_data_list(graph_list)
    return batch.x, batch.edge_index, batch.batch

def create_edge_index(ast):
    index_map = {}
    counter = [0]
    def index_callbck(node):
        index_map[node.meta] = counter[-1]
        counter.append(counter[-1]+1)
        
    traverse_postorder(ast, index_callbck)
    edge_index = []
    def callbck(node):
        for child in node.children:
            parent_child = [index_map[node.meta], index_map[child.meta]]
            child_parent = [index_map[child.meta], index_map[node.meta]]
            edge_index.append(parent_child)
            edge_index.append(child_parent)
    
    traverse_postorder(ast, callbck)
    if len(edge_index) == 0:
        return torch.empty(2, 0, dtype=torch.long)
    else:
        return torch.tensor(edge_index, dtype=torch.long).t().contiguous()
    
def one_hot_encode(ast, nonterminals):
    target = []
    def callbck(node):
        temp = [0.0]*len(nonterminals)
        index = nonterminals.index(node.data)
        temp[index] = 1.0
        target.append(temp)
    traverse_postorder(ast, callbck)
    return torch.tensor(target)

def state_id(state):
    goal = state[0]
    sexp = goal["sexp"] + "".join([c["sexp"] for c in state[1]])
    return sha1(sexp.encode("utf-8")).hexdigest()

def get_reward(opts, res):
    if res == 'ERROR':
        r = opts.error_punishment
    elif res in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED']:
        r = opts.error_punishment
    elif res == 'SUCCESS':
        r = opts.success_reward
    else:
        r = opts.neutral_reward
    return r


def proof_end(state):
    return state['result'] in ['MAX_NUM_TACTICS_REACHED', 'MAX_TIME_REACHED', 'SUCCESS']


def is_equivalent(opts, tac, action, state):
    goal, lc, gc = state[0], state[1], state[2]
    lc_ids = [c['ident'] for c in lc]
    gc_arg = find_gc_arg(opts, tac, lc_ids)
    lc_arg = find_lc_arg(opts, tac, lc_ids)

    if gc_arg == None and lc_arg == None:
        return tac == action
    elif lc_arg == None:
        tac_elements = tac.split(' ')
        for tac_element in tac_elements:
            if tac_element not in action:
                return False
        return True
    elif gc_arg == None:
        return tac == action

    return False

def find_gc_arg(opts, tactic_application, lc_ids):
    with open(opts.generic_args) as f: generic_args = json.load(f)
    with open(opts.tactics) as f: tactics = json.load(f)
    all_actions = tactic_application.split(" ")
    args = all_actions[1:]
    for arg in args:
        if arg in generic_args:
            continue
        if arg in tactics:
            continue
        if arg in lc_ids:
            continue
        return arg
    return None

def find_lc_arg(opts, tactic_application, lc_ids):
    all_actions = tactic_application.split(" ")
    args = all_actions[1:]
    for arg in args:
        if arg in lc_ids:
            return arg
    return None