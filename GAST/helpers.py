import os, random, pickle, logging, json
from glob import glob
from torch.utils.data import Dataset
import torch
from torch_geometric.data import Data, Batch
from gallina import traverse_postorder

def files_on_split(root, projs_split):
    train_files, valid_files, test_files = [], [], []
    
    for proj in projs_split["projs_train"]:
        train_files.extend(glob(os.path.join(root, f"{proj}/**/*.json"), recursive=True))
        
    for proj in projs_split["projs_valid"]:
        valid_files.extend(glob(os.path.join(root, f"{proj}/**/*.json"), recursive=True))
        
    for proj in projs_split["projs_test"]:
        test_files.extend(glob(os.path.join(root, f"{proj}/**/*.json"), recursive=True))
    
    return train_files, valid_files, test_files
    
class ProofStepData(Dataset):
    def __init__(self, opts, split):
        super().__init__()
        self.opts = opts
        self.split = split
        self.datapath = self.opts.datapath
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
        
        
def setup_loggers(opts):
    try:
        os.remove(opts.run_log)
        os.remove(opts.res_log)
    except:
        pass
                        
    run_handler = logging.FileHandler(opts.run_log)
    res_handler = logging.FileHandler(opts.res_log)
    
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


def get_tactic_targets(opts, tactics_json, batch):
    tactics = get_true_tactics(batch)            
    targets = torch.empty(len(tactics), dtype=torch.long).to(opts.device)
    for i, tactic in enumerate(tactics):
        index = -1
        if tactic in tactics_json:
            index = tactics_json.index(tactic)
            targets[i] = index
        else:
            for j, supported_tactic in enumerate(tactics_json):
                if supported_tactic in tactic:
                    index = j
                    targets[i] = index
            if index == -1:
               print(tactic)          
    return targets  

def get_true_tactics(batch):
    tactic_applications = [tactic['text'] for tactic in batch['tactic']]
    tactics = []
    for tactic_application in tactic_applications:
        if tactic_application.startswith("simple induction"):
            tactics.append("simple induction")
        else:
            all_actions = tactic_application.split(" ")
            tactics.append(all_actions[0])
    return tactics
    
def get_true_args(batch):
    tactic_applications = [tactic['text'] for tactic in batch['tactic']]
    args = []
    for tactic_application in tactic_applications:
        all_actions = tactic_application.split(" ")
        tmp = []
        for action in all_actions[1:]:
            tmp.append(action)
        args.append(tmp)
    return args   
    
def get_pred_tactics(tactics, probs):
    res = []
    for prob in probs:
        pred = tactics[torch.argmax(prob)]
        res.append(pred)
    return res
    
def build_csv(opts, train_loss, valid_loss, train_acc, valid_acc):
    path = opts.res_csv
    f = open(path, 'a')
    f.write(f"{train_loss},{valid_loss},{train_acc},{valid_acc}\n")
    f.close()


def prep_single_batch_asts(opts, asts):
    with open(opts.nonterminals) as f: nonterminals = json.load(f)

    graph_list = []
    edge_index = create_edge_index(asts[0])
    x = one_hot_encode(asts[0], nonterminals)
    for i in range(1, 11):
        if i < len(asts) and asts[i] != None:
            ast = asts[i]
            current_edge_index = create_edge_index(ast)
            current_x = one_hot_encode(ast, nonterminals)
        else:
            current_edge_index = torch.tensor([[]], dtype=torch.long).t().contiguous()
            current_x = torch.zeros(len(nonterminals)).to(opts.device)

        edge_index = torch.cat([edge_index, current_edge_index])
        x = torch.cat([x, current_x])

    data = Data(x=x, edge_index=edge_index).to(opts.device)
    graph_list.append(data) 
    batch = Batch().from_data_list(graph_list)
    return batch.x, batch.edge_index, batch.batch

def prep_asts(opts, asts, length):
    with open(opts.nonterminals) as f: nonterminals = json.load(f)
    graph_list = []
    for i, ast in enumerate(asts):
        if ast != None:
            edge_index = create_edge_index(ast)
            if edge_index.size()[0] != 2:
                edge_index = torch.empty(2, 0, dtype=torch.long)

            x = one_hot_encode(ast, nonterminals)
            data = Data(x=x, edge_index=edge_index).to(opts.device)
            graph_list.append(data)
        
        if i >= length-1:
            break

    while len(graph_list) < length:
        x = torch.empty(1, len(nonterminals), dtype=torch.long)
        edge_index = torch.empty(2, 0, dtype=torch.long)
        data = Data(x=x, edge_index=edge_index).to(opts.device)
        graph_list.append(data)

    batch = Batch().from_data_list(graph_list).to(opts.device)
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

def get_gc_targets(opts, batch):
    tactic_application = [t["text"] for t in batch["tactic"]][0]
    lc_ids = [[c["ident"] for c in lc] for lc in batch["local_context"]][0]
    gc_ids = [[c["qualid"] for c in gc] for gc in batch["env"]][0]

    target = find_gc_arg(opts, tactic_application, lc_ids)
 
    res = torch.zeros(len(batch["goal"]), dtype=torch.long).to(opts.device)
    index = 0
    true = None
    for i, gc_id in enumerate(gc_ids):
        if target in gc_id:
            index = i
            true = target

    res[0] = index

    return res, [true]

def get_lc_targets(opts, batch):
    tactic_application = [t["text"] for t in batch["tactic"]][0]
    lc_ids = [[c["ident"] for c in lc] for lc in batch["local_context"]][0]
    gc_ids = [[c["qualid"] for c in gc] for gc in batch["env"]][0]

    target = find_lc_arg(opts, tactic_application, lc_ids)
 
    res = torch.zeros(len(batch["goal"]), dtype=torch.long).to(opts.device)
    index = 0
    true = None
    for i, lc_id in enumerate(lc_ids):
        if target in lc_id:
            index = i
            true = target

    res[0] = index

    return res, [true]

def get_pred_gc(opts, batch, probs):
    preds = []
    for gc in batch["env"]:
        gc_ids = [c["qualid"] for c in gc]
        
        index = torch.argmax(probs)
        if index >= len(gc_ids):
            return ["None"]
        preds.append(gc_ids[index])

    return preds

def get_pred_lc(opts, batch, probs):
    preds = []
    for lc in batch["local_context"]:
        lc_ids = [c["ident"] for c in lc]
        
        index = torch.argmax(probs)
        if index >= len(lc_ids):
            return ["None"]
        preds.append(lc_ids[index])

    return preds


def prep_tac(opts, tactic, arg_probs):
    gc_arg = arg_probs["gc"][max(arg_probs["gc"].keys())]
    lc_arg = arg_probs["lc"][max(arg_probs["lc"].keys())]      

    # intro
    if tactic == "intro":
        return "intros"

    # specialize
    if tactic == "specialize":
        return f"specialize ({lc_arg} {gc_arg})"

    # froced theorem
    if tactic in ["apply", "rewrite", "unfold", "destruct", "elim", "case", "generalize", "exact"]:
        tactic = f"{tactic} {gc_arg}"
    # optional theorem
    elif tactic in ["auto", "simple_induction", "eauto"]:
        tactic = tactic

    # forced assumption
    if tactic in ["induction", "exists", "revert", "inversion_clear", "injection", "contradict"]:
        tactic = f"{tactic} {lc_arg}"
    # optional assumption
    elif tactic in ["apply", "rewrite", "simpl", "unfold", "clear", "subst", "red", "discriminate", "inversion", "hnf", "contradiction"]:
        tactic = tactic

    # hind db
    if tactic in ["auto", "eauto"]:
        tactic = f"{tactic} with *"

    """
    if opts.all:
        tactic = f"all: {tactic}"
    """

    return tactic


def is_s(batch):
    steps = batch["step"]
    for step in steps:
        if not step["is_synthetic"]:
            return False
    return True