import os, random, pickle, logging
from glob import glob
from torch.utils.data import Dataset
import torch


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
    
    
    
    
    