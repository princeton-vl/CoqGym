import argparse, sys, os, torch, gc
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import helpers
from torch.utils.data import DataLoader

from nn_model.gast_tac import GastTac
from nn_model.trans_tac import TransTac

def goodtogo(opts, batch):
    assert len(batch['is_synthetic']) == 1
    is_synthetic = batch['is_synthetic'][0]
    if "human" in opts.model and is_synthetic:
        return False
    elif "synthetic" in opts.model and not is_synthetic:
        return False
    return True

def pick_model(opts):
    if "gast" in opts.model:
        model = GastTac(opts)
    else:
        model = TransTac(opts)
    return model

parser = argparse.ArgumentParser()

# paths
parser.add_argument("--nonterminals", type=str, default="./jsons/nonterminals.json")
parser.add_argument("--tactics", type=str, default="./jsons/tactics.json")
parser.add_argument("--generic_args", type=str, default="./jsons/generic_args.json")
parser.add_argument("--split", type=str, default="../projs_split.json")
parser.add_argument("--sexp_cache", type=str, default="../sexp_cache")
    
# run env
parser.add_argument("--num_workers", type=int, default=2)
parser.add_argument("--batchsize", type=int, default=1)

# data
parser.add_argument("--datapath", type=str, default="../proof_steps") # ../ASTactic/proof_steps
parser.add_argument("--proof_type", type=str, default="human")

# optimizer
parser.add_argument("--lr", type=float, default=1e-3)
parser.add_argument("--l2", type=float, default=1e-6)
parser.add_argument("--lr_reduce_patience", type=int, default=3)
parser.add_argument("--optimizer", type=str, default="adam")
parser.add_argument("--scheduler", type=str, default="plateau")

# model
parser.add_argument('--model', type=str, default='gast')
parser.add_argument("--dropout", type=float, default=0.0)
    
# gast
parser.add_argument("--embedding_dim", type=int, default=256)
parser.add_argument("--sortk", type=int, default=30)

# trans
parser.add_argument("--num_hidden", type=int, default=6)
parser.add_argument("--num_attention", type=int, default=6)
parser.add_argument("--tokenizer_length", type=int, default=512)
    
opts = parser.parse_args()
opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
opts.savepath = f"./models/{helpers.get_core_path(opts)}"

run_log, res_log = helpers.setup_loggers(opts)

datapath = opts.datapath
filepath = f"{datapath}/valid"
files = os.listdir(filepath)
valid_files = []
for i, file_name in enumerate(files):
    current_file_path = f"{filepath}/{file_name}"
    valid_files.append(current_file_path)
    
valid = DataLoader(helpers.ProofStepData(valid_files), opts.batchsize, collate_fn=helpers.merge, num_workers = opts.num_workers)

if opts.model == "gast_human":
    tacmodel_path = "./models/best/acc/human/gast_tac.pth"
elif opts.model == "gast_synthetic":
    tacmodel_path = "./models/best/acc/synthetic/gast_tac.pth"
elif opts.model == "trans_human":
    tacmodel_path = "./models/best/acc/human/trans_tac.pth"
else:
    tacmodel_path = "./models/best/acc/synthetic/trans_tac.pth"


if str(opts.device) == "cpu":
    run_log.info(f"using CPU")
    run_log.info(f"torch uses {torch.get_num_threads()} theards")
    run_log.info(f"max recurssion is {sys.getrecursionlimit()}")

    taccheck = torch.load(tacmodel_path, map_location="cpu")
else:
    run_log.info("using GPU")
    run_log.info(f"torch uses {torch.get_num_threads()} theards")
    run_log.info(f"max recurssion is {sys.getrecursionlimit()}")

    taccheck = torch.load(tacmodel_path)

model = pick_model(opts)
model.load_state_dict(taccheck["state_dict"])
model.to(opts.device)
model.eval()


run_log.info(opts)
run_log.info(f"valid size -> {len(valid)}")
run_log.info(model)

num_correct = 0
for i, batch in enumerate(valid):
    if not goodtogo(opts, batch):
        continue
    preds, true, loss = model(batch)

    gc.collect()

    for j in range(len(batch["goal"])):
        if preds[j] == true[j]:
            num_correct += 1

        res_log.info(f"[{preds[j]}, {true[j]}]")

    run_log.info(f"{i}/{len(valid)} -> {round(100*(i/len(valid)), 8)}%")

res_log.info(f"NUM CORRECT: {num_correct}")
