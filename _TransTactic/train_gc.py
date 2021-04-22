import argparse, os, sys, torch, gc
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

from datetime import datetime
from torch.utils.data import DataLoader
from torch.optim.lr_scheduler import ReduceLROnPlateau
import numpy as np
import random

from helpers import ProofStepData, merge, setup_loggers, build_csv, find_gc_arg, is_s
from model.gcmodel import TransGCModel
from agent import Agent

def train(opts):
    
    torch.manual_seed(opts.seed)
    np.random.seed(opts.seed)
    random.seed(opts.seed)
    
    # log setup
    run_log, res_log = setup_loggers(opts)
                            
    # agent and provers
    model = TransGCModel(opts)
    model.to(opts.device)
    
    # dataloaders
    train = DataLoader(ProofStepData(opts, "train"), opts.batchsize, collate_fn=merge, num_workers = opts.num_workers)
    valid = DataLoader(ProofStepData(opts, "valid"), opts.batchsize, collate_fn=merge, num_workers = opts.num_workers)
    
    # optimizer
    optimizer = torch.optim.Adam(model.parameters(), lr=opts.lr, weight_decay=opts.l2)
    scheduler = ReduceLROnPlateau(optimizer, patience=opts.lr_reduce_patience, verbose=True)
    
    # log
    if str(opts.device) == "cpu":
        res_log.info(f"using CPU")
        res_log.info(f"torch uses {torch.get_num_threads()} theards")
        res_log.info(f"max recurssion is {sys.getrecursionlimit()}")
    else:
        res_log.info("using GPU")
        res_log.info(f"torch uses {torch.get_num_threads()} theards")
        res_log.info(f"max recurssion is {sys.getrecursionlimit()}")
        
    res_log.info(f"opts -> {opts}")
    start_time = datetime.now()
    timestamp = str(start_time)[:-7].replace(" ", "-")
    res_log.info(f"training size -> {len(train)}")
    res_log.info(f"valid size -> {len(valid)}")
    res_log.info(model)
    
    # epochs
    for n in range(opts.epochs):
        run_log.info(f"epoch: {n}")
        
        # training stats
        loss_avg_train = 0
        num_correct_train = 0
        #pred_freq_train = {}
        
        # training loop
        model.train()
        proof_counter = 0
        batch_counter = 0
        for i, batch in enumerate(train):
            if opts.proof_type == "synthetic":
                if not is_s(batch):
                    continue
            elif opts.proof_type == "human":
                if is_s(batch):
                    continue
            
            if not check_args(opts, batch):
                continue
            
            preds, true, loss = model(batch)
            
            loss.backward()
            optimizer.step()
            optimizer.zero_grad()
            gc.collect()
            
            elapsed_time = datetime.now() - start_time
            run_log.info(f"{i}/{len(train)} -> {100*(i/len(train))}% ({elapsed_time})")
            
            # update stats
            loss_avg_train += loss.item()    
            for j in range(len(batch["goal"])):
                if "." in preds[j]:
                    for element in preds[j].split("."):
                        if element == true[j]:
                            num_correct_train += 1
                elif true[j] in preds[j]:
                    num_correct_train += 1
                #pred_freq_train[preds[j]] = pred_freq_train.get(preds[j], 0) + 1
                proof_counter += 1
            batch_counter += 1
            
            if int(opts.lm[0]) != -1 and proof_counter >= int(opts.lm[0]):
                break
                
        loss_avg_train /= batch_counter
        acc_train = num_correct_train/proof_counter
        
        # save model
        torch.save({"state_dict": model.state_dict(), 
                    "n_epoch": n, 
                    "optimizer": optimizer.state_dict()},
                    f"{opts.savepath}%03d.pth" % n)
  
    
        # validation stats
        loss_avg_valid = 0
        num_correct_valid = 0
        #pred_freq_valid = {}
        
        # validation loop
        run_log.info("validation...")
        model.eval()
        proof_counter = 0
        batch_counter = 0
        for i, batch in enumerate(valid):
            if int(opts.lm[1]) != -1 and proof_counter >= int(opts.lm[1]):
                break

            if not check_args(opts, batch):
                continue
                
            preds, true, loss = model(batch)
            
            
            # update validation stats
            loss_avg_valid += loss.item()
            for j in range(len(batch["goal"])):
                if "." in preds[j]:
                    for element in preds[j].split("."):
                        if element == true[j]:
                            num_correct_valid += 1
                elif true[j] in preds[j]:
                    num_correct_valid += 1
                #pred_freq_valid[preds[j]] = pred_freq_valid.get(preds[j], 0) + 1
                proof_counter += 1
            batch_counter += 1  
                          
            elapsed_time = datetime.now() - start_time
            run_log.info(f"{i}/{len(valid)} -> {100*(i/len(valid))}% ({elapsed_time})")
            
        loss_avg_valid /= max(batch_counter, 1)
        acc_valid = num_correct_valid/max(proof_counter, 1)
        
        # log results
        res_log.info(f"####### epoch: {n} #######")
        #res_log.info(f"train guesses: {pred_freq_train}")
        #res_log.info(f"validation guesses: {pred_freq_valid}")
        res_log.info(f"train losses: {loss_avg_train}")
        res_log.info(f"validation losses: {loss_avg_valid}")
        res_log.info(f"train accuracy: {acc_train}")
        res_log.info(f"validation accuracy: {acc_valid}")
        res_log.info("###################")
        build_csv(opts, loss_avg_train, loss_avg_valid, acc_train, acc_valid)
    
        # reduce LR
        scheduler.step(loss_avg_valid)

def check_args(opts, batch):
    tactic_applications = [t["text"] for t in batch["tactic"]]
    gc_ids = [[c["qualid"]for c in gc] for gc in batch["env"]]
    lc_ids = [[c["ident"] for c in lc] for lc in batch["local_context"]]
    
    for i, tactic_application in enumerate(tactic_applications):
        gc_arg = find_gc_arg(opts, tactic_application, lc_ids[i])

        gc_prepped_ids = []
        for gc_id in gc_ids[i]:
            for prepped_id in gc_id.split("."):
                gc_prepped_ids.append(prepped_id)

        if gc_arg not in gc_prepped_ids:
            return False

    return True


if __name__ == "__main__":
    
    parser = argparse.ArgumentParser()
    
    # paths
    parser.add_argument("--datapath", type=str, default="../proof_steps")
    parser.add_argument("--nonterminals", type=str, default="../jsons/nonterminals.json")
    parser.add_argument("--tactics", type=str, default="../jsons/tactics.json")
    parser.add_argument("--generic_args", type=str, default="../jsons/generic_args.json")
    parser.add_argument("--args", type=str, default="./jsons/args.json")
    parser.add_argument("--split", type=str, default="../projs_split.json")
    parser.add_argument("--sexp_cache", type=str, default="../sexp_cache")
    parser.add_argument("--savepath", type=str, default="./models/gc")
    parser.add_argument("--run_log", type=str, default="./logs/run_gc.log")
    parser.add_argument("--res_log", type=str, default="./logs/res_gc.log")
    parser.add_argument("--res_csv", type=str, default="./logs/res_gc.csv")
    
    # run env
    parser.add_argument("--num_workers", type=int, default=0)
    parser.add_argument("--epochs", type=int, default=100)
    parser.add_argument("--batchsize", type=int, default=1)
    parser.add_argument("--model", type=str, default="gast2")
    parser.add_argument("--argmodel", type=bool, default=False)
    parser.add_argument("--lm", nargs="+", default=[-1, -1])
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--step_types", type=str, default="human")
    
    # optimizer    
    parser.add_argument("--lr", type=float, default=1e-6)
    parser.add_argument("--l2", type=float, default=1e-6)
    parser.add_argument("--lr_reduce_patience", type=int, default=3)
    parser.add_argument("--optimizer", type=str, default="adam")
    parser.add_argument("--scheduler", type=str, default="plateau")

    # model
    parser.add_argument("--dropout", type=float, default=0.5)
    parser.add_argument("--embedding_info", type=str, default="goal")
    
    parser.add_argument("--embedding_dim", type=int, default=512)
    parser.add_argument("--num_hidden", type=int, default=6)
    parser.add_argument("--num_attention", type=int, default=6)
    parser.add_argument("--tokenizer_length", type=int, default=512)
    
    opts = parser.parse_args()
    opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    
    train(opts)
