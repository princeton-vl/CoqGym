import os, logging, random, pickle, torch, json
from torch_geometric.data import Data, Batch
from torch.utils.data import Dataset
from gallina import traverse_postorder

def get_core_path(opts):
    path = ""
    if 'gast' in opts.model_type:
        path = f"{path}/gast"
    else:
        path = f"{path}/trans"
    if "human" in opts.proof_type:
        path = f"{path}/human"
    elif "synthetic" in opts.proof_type:
        path = f"{path}/synthetic"
    else:
        path = f"{path}/all"
    if "tac" in opts.model_type:
        path = f"{path}/tac"
    elif "lc" in opts.model_type:
        path = f"{path}/lc"
    else:
        path = f"{path}/gc"

    return path

def setup_loggers(opts):
    core = get_core_path(opts)
    run_path, res_path = f"./logs/{core}_run.log", f"./logs/{core}_res.log"

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

def build_csv(opts, train_loss, valid_loss, train_acc, valid_acc):
    path = f"./logs/{get_core_path(opts)}.csv"
    f = open(path, 'a')
    f.write(f"{train_loss},{valid_loss},{train_acc},{valid_acc}\n")
    f.close()


def find_lc_arg(opts, tactic_application, lc_ids):
    all_actions = tactic_application.split(" ")
    args = all_actions[1:]
    for i, arg in enumerate(args):
        if arg in lc_ids:
            return arg, lc_ids.index(arg)
    return None, -1


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



                    
def check_lc(opts, example):
    tactic_app = example['tactic']['text']
    lc_ids = [c['ident'] for c in example['local_context']]
    lc_arg, index = find_lc_arg(opts, tactic_app, lc_ids)
    if lc_arg == None or index >= 50:
        return False
    return True

def check_gc(opts, example):
    tactic_app = example['tactic']['text']
    lc_ids = [c['ident'] for c in example['local_context']]
    gc_ids = [c['qualid'] for c in example['env']]
    gc_arg = find_gc_arg(opts, tactic_app, lc_ids)
    gc_prepped_ids = []
    for gc_id in gc_ids:
        for prepped_id in gc_id.split("."):
            gc_prepped_ids.append(prepped_id)
    if gc_arg not in gc_prepped_ids:
        return False
    return True

def filter_f(opts, path):
    with open(path, 'rb') as f:
        example = pickle.load(f)
        is_synthetic = example['is_synthetic']
        valid_lc = check_lc(opts, example)
        valid_gc = check_gc(opts, example)
        if opts.proof_type == 'synthetic' and not is_synthetic:
            return False
        elif opts.proof_type == 'human' and is_synthetic:
            return False
        if 'lc' in opts.model_type and not valid_lc:
            return False
        elif 'gc' in opts.model_type and not valid_gc:
            return False
    return True
            

def get_files(opts, split):
    datapath = opts.datapath
    filepath = f"{datapath}/{split}"
    files = os.listdir(filepath)
    res = []
    for i, file_name in enumerate(files):
        current_file_path = f"{filepath}/{file_name}"
        if filter_f(opts, current_file_path):
            res.append(current_file_path)
    return res


class ProofStepData(Dataset):
    def __init__(self, files):
        super().__init__()
        self.files = files
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


def tweak_opts(opts):
    if 'trans' in opts.model_type:
        opts.lr = 1e-5

    return opts

def get_tactic_targets(opts, tactics_json, batch):
    tactics = get_tactics_true(batch)            
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


def get_tactics_true(batch):
    tactic_applications = [tactic['text'] for tactic in batch['tactic']]
    tactics = []
    for tactic_application in tactic_applications:
        if tactic_application.startswith("simple induction"):
            tactics.append("simple induction")
        else:
            all_actions = tactic_application.split(" ")
            tactics.append(all_actions[0])
    return tactics


def get_args_true(batch):
    tactic_applications = [tactic['text'] for tactic in batch['tactic']]
    args = []
    for tactic_application in tactic_applications:
        all_actions = tactic_application.split(" ")
        tmp = []
        for action in all_actions[1:]:
            tmp.append(action)
        args.append(tmp)
    return args


def get_tactics_pred(tactics, probs):
    res = []
    for prob in probs:
        pred = tactics[torch.argmax(prob)]
        res.append(pred)
    return res


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


def get_gc_targets(opts, batch):
    tactic_applications = [t["text"] for t in batch["tactic"]]
    lc_ids_s = [[c["ident"] for c in lc] for lc in batch["local_context"]]
    gc_ids_s = [[c["qualid"] for c in gc] for gc in batch["env"]]
    
    res = torch.zeros(len(batch["goal"]), dtype=torch.long).to(opts.device)
    trues = []

    for i in range(len(tactic_applications)):
        tactic_application = tactic_applications[i]
        lc_ids = lc_ids_s[i]
        gc_ids = gc_ids_s[i]
        target = find_gc_arg(opts, tactic_application, lc_ids)
        index = 0
        true = None
        for j, gc_id in enumerate(gc_ids):
            if target in gc_id:
                index = j
                true = target

        res[i] = index
        trues.append(true)

    return res, trues

def get_lc_targets(opts, batch):
    tactic_applications = [t["text"] for t in batch["tactic"]]
    lc_ids_s = [[c["ident"] for c in lc] for lc in batch["local_context"]]

    res = torch.zeros(len(batch["goal"]), dtype=torch.long).to(opts.device)
    trues = []

    for i in range(len(tactic_applications)):
        tactic_application = tactic_applications[i]
        lc_ids = lc_ids_s[i]
        target, _ = find_lc_arg(opts, tactic_application, lc_ids)
        index = 0
        true = None
        for j, lc_id in enumerate(lc_ids):
            if target in lc_id:
                index = j
                true = target
        res[i] = index
        trues.append(true)
    return res, trues

def get_gc_pred(opts, batch, probs):
    preds = []
    for i, gc in enumerate(batch["env"]):
        gc_ids = [c["qualid"] for c in gc]
        
        index = torch.argmax(probs[i])
        if index >= len(gc_ids):
            preds.append("None")
            continue
        preds.append(gc_ids[index])

    return preds

def get_lc_pred(opts, batch, probs):
    preds = []
    for i, lc in enumerate(batch["local_context"]):
        lc_ids = [c["ident"] for c in lc]
        
        index = torch.argmax(probs[i])
        if index >= len(lc_ids):
            preds.append("None")
            continue

        preds.append(lc_ids[index])

    return preds


def check_correctness(opts, pred, true):
    if 'tac' in opts.model_type or 'lc' in opts.model_type:
        return pred == true
    else:
        if "." in pred:
            for element in pred.split("."):
                if element == true:
                    return True
        elif true in pred:
            return True
    return False
