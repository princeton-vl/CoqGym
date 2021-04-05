import argparse, os, sys, torch, json
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))
from agent import Agent
import numpy as np
import random
from ffn.tacmodel import FFNTacModel
from ffn.argmodel import FFNArgModel
from datetime import datetime
from helpers import setup_loggers, files_on_split
from eval_env import FileEnv


if __name__ == "__main__":
    
    parser = argparse.ArgumentParser()
    
    # paths
    parser.add_argument("--tacmodel", type=str, default="./models/dummy.pth")
    parser.add_argument("--argmodel", type=str, default="./models/dummy.pth")
    parser.add_argument("--model", type=str, default="ffn")
    parser.add_argument("--datapath", type=str, default="../data")
    parser.add_argument("--nonterminals", type=str, default="./jsons/nonterminals.json")
    parser.add_argument("--tactics", type=str, default="./jsons/tactics.json")
    parser.add_argument("--split", type=str, default="../projs_split.json")
    parser.add_argument("--sexp_cache", type=str, default="../sexp_cache")
    parser.add_argument("--run_log", type=str, default="./logs/run.log")
    parser.add_argument("--res_log", type=str, default="./logs/res.log")
    
    
    # run env
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--num_tac_candidates", type=int, default=10)
    parser.add_argument("--tac_on_all_subgoals", type=bool, default=False)
    parser.add_argument("--depth_limit", type=int, default=10)
    parser.add_argument("--lm", type=int, default=-1)
    parser.add_argument("--max_num_tacs", type=int, default=300)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--draw", type=bool, default=False)
    
    # model parameters
    parser.add_argument("--dropout", type=str, default=0.0)
    opts = parser.parse_args()
    opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    # set run env
    torch.manual_seed(opts.seed)
    np.random.seed(opts.seed)
    random.seed(opts.seed)
    
    # log setup
    run_log, res_log = setup_loggers(opts)
                     
    # models and agent
    if opts.model == "ffn":
        tacmodel = FFNTacModel(opts)            
        if opts.device.type == "cpu":
            taccheck = torch.load(opts.tacmodel, map_location="cpu")
        else:
            taccheck = torch.load(opts.tacmodel)
        tacmodel.load_state_dict(taccheck["state_dict"])
        tacmodel.to(opts.device)
        tacmodel.eval()
    agent = Agent(opts, tacmodel=tacmodel, argmodel=None)
    
    # log
    if str(opts.device) == "cpu":
        res_log.info(f"using CPU")
        res_log.info(f"torch uses {torch.get_num_threads()} theards")
        res_log.info(f"max recurssion is {sys.getrecursionlimit()}")
    else:
        res_log.info("using GPU")
        res_log.info(f"torch uses {torch.get_num_threads()} theards")
        res_log.info(f"max recurssion is {sys.getrecursionlimit()}")
    res_log.info(opts)
    res_log.info(tacmodel)
    start_time = datetime.now()
    
    # testing
    train_files, valid_files, test_files = files_on_split(opts.datapath, json.load(open(opts.split, "r")))
    
    total_count = 0
    file_count = 0
    correct = 0
    last_proj = test_files[0].split("/")[-2]
    proj_count = 0
    proj_correct = 0
    for f in test_files:
        current_proj = f.split("/")[-2]
        if current_proj != last_proj:
            last_proj_count = proj_count
            last_proj_correct = proj_correct
            proj_count = 0
            proj_correct = 0    
        
        current_count = 0
        current_correct = 0
        with FileEnv(f, max_num_tactics=opts.max_num_tacs, timeout=opts.timeout) as file_env:
            for proof_env in file_env:
                proof_name = proof_env.proof["name"]
                res = agent.test(proof_env)
                total_count += 1
                current_count += 1
            
                if res["proved"]:
                    current_correct += 1
                    correct += 1
            
                if opts.lm <= total_count and opts.lm > -1:
                    break
                    
                elapsed_time = datetime.now() - start_time
                run_log.info(f"{total_count}/{10000} -> {100*(total_count/10000)}% ({elapsed_time})")
        
        file_count += 1
        
        
        proj_count += current_count
        proj_correct += current_correct
        if current_proj != last_proj:
            proj_acc = last_proj_correct/last_proj_count
            res_log.info(f"{last_proj}: \t\t\t {last_proj_correct}/{last_proj_count} \t ({proj_acc})")
            res_log.info("-----------------")
        
        acc = current_correct/current_count
        res_log.info(f"{f}: \t\t\t {current_correct}/{current_count} \t ({acc})")
        
        last_proj = current_proj
        
        if opts.lm <= total_count and opts.lm > -1:
            break
    
    acc = total_correct/total_count
    res_log.info(f"Total: \t\t {total_correct}/{total_count} \t ({acc})")
        
        
    
