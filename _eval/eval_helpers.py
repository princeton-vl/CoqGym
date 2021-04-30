import os, logging, json, torch, pickle, random
from glob import glob
from utils import SexpCache
from gallina import GallinaTermParser, traverse_postorder
from hashlib import sha1
from torch_geometric.data import Data, Batch
from torch.utils.data import Dataset
from lark import Tree

sexp_cache = SexpCache('../sexp_cache', readonly=True)
term_parser = GallinaTermParser(caching=True)

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
        local_contexts.append(padd_lc(local_context))

    return goals[0], local_contexts[0]

def process_global_context(state):
    global_context = []
    toplevel_consts = [const for const in state['env']['constants'] if const['qualid'].startswith('SerTop')]

    for const in toplevel_consts[-10:]:
        ast = sexp_cache[const['sexp']]
        global_context.append({'qualid': const['qualid'], 'text': const['type'], 'ast': term_parser.parse(ast), 'sexp': const['sexp']})
    
    return padd_gc(global_context)

def padd_gc(c):
    if len(c) > 10:
        return c[0:10]
        
    while len(c) < 10:
        empty = {'ident': '', 'text': '', 'ast': Tree(data="constr__constr", children=[]), 'sexp': ''}
        c.append(empty)

    return c

def padd_lc(c):
    if len(c) > 10:
        return c[0:10]
        
    while len(c) < 10:
        empty = {'ident': '', 'text': '', 'ast': Tree(data"constr__constr", children=[]), 'sexp': ''}
        c.append(empty)

    return c

def state_id(state):
    goal = state[0]
    sexp = goal["sexp"] + "".join([c["sexp"] for c in state[1]])
    return sha1(sexp.encode("utf-8")).hexdigest()

def get_core_path(opts):
    
    if opts.model_type == "rl":
        path = f"rl/{opts.rl_model}/"
    elif opts.model_type == "sl":
        path = f"sl/{opts.sl_model}/"

    return path

def setup_loggers(opts):
    core = get_core_path(opts)
    run_path, res_path = f"./logs/{core}run.log", f"./logs/{core}res.log"

    try:
        os.remove(run_path)
        os.remove(res_path)
    except:
        pass

    run_handler = logging.FileHandler(run_path)
    res_handler = logging.FileHandler(res_path)
    
    run_handler.setFormatter(logging.Formatter('%(asctime)s:\t%(message)s'))
    res_handler.setFormatter(logging.Formatter('%(asctime)s:\t%(message)s'))
    
    run_logger = logging.getLogger("run log")
    res_logger = logging.getLogger("test log")
    
    run_logger.addHandler(run_handler)
    res_logger.addHandler(res_handler)
    
    run_logger.setLevel(logging.INFO)
    res_logger.setLevel(logging.INFO)
    
    run_logger.propagate = False
    res_logger.propagate = False
    
    return run_logger, res_logger

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
