import argparse, sys, os, torch, gc
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import helpers
from torch.utils.data import DataLoader
from torch.optim.lr_scheduler import ReduceLROnPlateau

from nn_model.gast_tac import GastTac
from nn_model.gast_lc import GastLC
from nn_model.gast_gc import GastGC
from nn_model.trans_tac import TransTac
from nn_model.trans_lc import TransLC
from nn_model.trans_gc import TransGC


def pick_model(opts):
    if opts.model_type == 'gast_tac':
        model = GastTac(opts)
    elif opts.model_type == 'gast_lc':
        model = GastLC(opts)
    elif opts.model_type == 'gast_gc':
        model = GastGC(opts)
    elif opts.model_type == 'trans_tac':
        model = TransTac(opts)
    elif opts.model_type == 'trans_lc':
        model = TransLC(opts)
    elif opts.model_type == 'trans_gc':
        model = TransGC(opts)
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
parser.add_argument("--epochs", type=int, default=100)
parser.add_argument("--batchsize", type=int, default=4)

# data
parser.add_argument("--datapath", type=str, default="../proof_steps") # ../ASTactic/proof_steps
parser.add_argument("--proof_type", type=str, default="all")

# optimizer
parser.add_argument("--lr", type=float, default=1e-3)
parser.add_argument("--l2", type=float, default=1e-6)
parser.add_argument("--lr_reduce_patience", type=int, default=3)
parser.add_argument("--optimizer", type=str, default="adam")
parser.add_argument("--scheduler", type=str, default="plateau")

# model
parser.add_argument('--model_type', type=str, default='gast_tac')
parser.add_argument("--dropout", type=float, default=0.5)
    
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

opts = helpers.tweak_opts(opts)

run_log, res_log = helpers.setup_loggers(opts)

train_files = helpers.get_files(opts, "train", run_log)
valid_files = helpers.get_files(opts, "valid", run_log)
train = DataLoader(helpers.ProofStepData(train_files), opts.batchsize, collate_fn=helpers.merge, num_workers = opts.num_workers) # valid_files
valid = DataLoader(helpers.ProofStepData(valid_files), opts.batchsize, collate_fn=helpers.merge, num_workers = opts.num_workers)

model = pick_model(opts)
model.to(opts.device)

optimizer = torch.optim.Adam(model.parameters(), lr=opts.lr, weight_decay=opts.l2)
scheduler = ReduceLROnPlateau(optimizer, patience=opts.lr_reduce_patience, verbose=True)


if str(opts.device) == "cpu":
    res_log.info(f"using CPU")
    res_log.info(f"torch uses {torch.get_num_threads()} theards")
    res_log.info(f"max recurssion is {sys.getrecursionlimit()}")
else:
    res_log.info("using GPU")
    res_log.info(f"torch uses {torch.get_num_threads()} theards")
    res_log.info(f"max recurssion is {sys.getrecursionlimit()}")

res_log.info(opts)
res_log.info(f"training size -> {len(train)}")
res_log.info(f"valid size -> {len(valid)}")
res_log.info(model)


for n in range(opts.epochs):
    run_log.info(f"epoch: {n}")

    loss_avg_train = 0
    num_correct_train = 0
    proof_counter = 0
    batch_counter = 0
    model.train()
    for i, batch in enumerate(train):
        preds, true, loss = model(batch)

        loss.backward()
        optimizer.step()
        optimizer.zero_grad()
        gc.collect()

        run_log.info(f"{i}/{len(train)} -> {round(100*(i/len(train)), 8)}%")

        loss_avg_train += loss.item()
        batch_counter += 1
        for j in range(len(batch["goal"])):
            proof_counter += 1
            if helpers.check_correctness(opts, preds[j], true[j]):
                num_correct_train += 1
    
    loss_avg_train /= batch_counter
    acc_train = round(num_correct_train/proof_counter, 8)

    
    torch.save({"state_dict": model.state_dict(), 
                "n_epoch": n, 
                "optimizer": optimizer.state_dict()},
                f"{opts.savepath}%03d.pth" % n)
    

    run_log.info("validation...")
    loss_avg_valid = 0
    num_correct_valid = 0
    proof_counter = 0
    batch_counter = 0
    model.eval()
    for i, batch in enumerate(valid):
        preds, true, loss = model(batch)

        gc.collect()

        loss_avg_valid += loss.item()
        batch_counter += 1 
        for j in range(len(batch["goal"])):
            proof_counter += 1
            if helpers.check_correctness(opts, preds[j], true[j]):
                num_correct_valid += 1

        run_log.info(f"{i}/{len(valid)} -> {round(100*(i/len(valid)), 8)}%")
                
    loss_avg_valid /= batch_counter
    acc_valid = round(num_correct_valid/proof_counter, 8)


    # log results
    res_log.info(f"####### epoch: {n} #######")
    res_log.info(f"train losses: {loss_avg_train}")
    res_log.info(f"validation losses: {loss_avg_valid}")
    res_log.info(f"train accuracy: {acc_train}")
    res_log.info(f"validation accuracy: {acc_valid}")
    res_log.info("###################")
    helpers.build_csv(opts, loss_avg_train, loss_avg_valid, acc_train, acc_valid)
    
    # reduce LR
    scheduler.step(loss_avg_valid)