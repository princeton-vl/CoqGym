import argparse, os, sys, torch, json
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))
from agent import Agent
import numpy as np
import random
from model.tacmodel import GuesserTacModel
from datetime import datetime
from helpers import setup_loggers, files_on_split
from eval_env import FileEnv


if __name__ == "__main__":
    
    parser = argparse.ArgumentParser()
    
    # paths
    parser.add_argument("--datapath", type=str, default="../data")
    parser.add_argument("--tactics", type=str, default="./jsons/tactics.json")
    parser.add_argument("--split", type=str, default="../projs_split.json")
    parser.add_argument("--sexp_cache", type=str, default="../sexp_cache")
    parser.add_argument("--run_log", type=str, default="./logs/run.log")
    parser.add_argument("--res_log", type=str, default="./logs/eval.log")
    parser.add_argument("--pngpath", type=str, default="./pngs/")
    
    # run env
    parser.add_argument("--jupyter", type=bool, default=False)
    parser.add_argument("--lm", nargs="+", default=[-1, -1])
    parser.add_argument("--num_tac_candidates", type=int, default=10)
    parser.add_argument("--tac_on_all_subgoals", type=bool, default=False)
    parser.add_argument("--depth_limit", type=int, default=50)
    parser.add_argument("--max_num_tacs", type=int, default=300)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--draw", type=bool, default=False)
    
    # model parameters
    opts = parser.parse_args()
    opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    
    # log setup
    run_log, res_log = setup_loggers(opts)
                     
    # models and agent
    tacmodel = GuesserTacModel(opts)
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
    last_proj = test_files[0].split("/")[2]
    proj_count = 0
    proj_correct = 0
    total_proj_count = 0
    for f in test_files:
        current_proj = f.split("/")[2]
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
                print(proof_name)
                res = agent.test(proof_env)
                
                total_count += 1
                current_count += 1
            
                if res["proved"]:
                    current_correct += 1
                    correct += 1
                    
                if opts.draw and not opts.jupyter:
                    graph = res["graph"]
                    graph.render(f"{opts.pngpath}/{proof_name}", format="png", cleanup=True)
            
                if int(opts.lm[0]) <= current_count and int(opts.lm[0]) > -1:
                    break
                            
        file_count += 1
              
        proj_count += current_count
        proj_correct += current_correct
        if current_proj != last_proj:
            total_proj_count += 1
            proj_acc = last_proj_correct/last_proj_count
            res_log.info(f"{last_proj}: \t {last_proj_correct}/{last_proj_count} ({proj_acc})".expandtabs(100))
            res_log.info("-----------------")
        
        print(file_count/len(test_files))
        acc = current_correct/current_count
        res_log.info(f"{f}: \t {current_correct}/{current_count} ({acc})".expandtabs(100))
        
        last_proj = current_proj
        if int(opts.lm[1]) <= total_proj_count and int(opts.lm[1]) > -1:
            break
    
    acc = correct/total_count
    res_log.info(f"Total: \t {correct}/{total_count} ({acc})".expandtabs(100))
