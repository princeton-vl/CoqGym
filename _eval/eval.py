import argparse, os, sys, torch, json, traceback
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import eval_helpers
from eval_env import FileEnv

from rl_agent import RLAgent
from sl_agent import SLAgent


parser = argparse.ArgumentParser()
parser.add_argument("--data", type=str, default="../data")
parser.add_argument("--nonterminals", type=str, default="../_RL/jsons/nonterminals.json")
parser.add_argument("--tactics", type=str, default="../_RL/jsons/tactics.json")
parser.add_argument("--split", type=str, default="../projs_split.json")
parser.add_argument("--sexp_cache", type=str, default="../sexp_cache")

parser.add_argument("--depth_limit", type=int, default=50)
parser.add_argument("--max_num_tacs", type=int, default=300)
parser.add_argument("--timeout", type=int, default=600)

parser.add_argument("--dropout", type=str, default=0.0)

# gast
parser.add_argument("--embedding_dim", type=int, default=256)
parser.add_argument("--sortk", type=int, default=30)

# trans
parser.add_argument("--num_hidden", type=int, default=6)
parser.add_argument("--num_attention", type=int, default=6)
parser.add_argument("--tokenizer_length", type=int, default=512)

parser.add_argument("--model_type", type=str, default="sl")
parser.add_argument("--sl_model", type=str, default="gast_human")
parser.add_argument("--rl_model", type=str, default="")

opts = parser.parse_args()
opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

run_log, res_log = eval_helpers.setup_loggers(opts)
res_log.info(opts)

if opts.model_type == "sl":
    agent = SLAgent(opts, res_log)
elif opts.model_type == "rl":
    agent = RLAgent(opts, res_log)


_, _, test_files = eval_helpers.files_on_split(opts)

total_count = 0
file_count = 0
proj_count = 0
total_proj_count = 0
skipped = 0
correct = 0
proj_correct = 0
last_proj = test_files[0].split("/")[2]
for f in test_files:
    current_proj = f.split("/")[2]
    if current_proj != last_proj:
        last_proj_count = proj_count
        last_proj_correct = proj_correct
        proj_count = 0
        proj_correct = 0    
        
    current_count = 0
    current_correct = 0
    try:
        with FileEnv(f, max_num_tactics=opts.max_num_tacs, timeout=opts.timeout) as file_env:
            for proof_env in file_env:
                proof_name = proof_env.proof["name"]
                res, script = agent.test(proof_env)

                total_count += 1
                current_count += 1
                if res:
                    current_correct += 1
                    correct += 1

                run_log.info(f'Seen {total_count} ({round(total_count/13137, 8)} %) of proofs')
    except:
        run_log.info(traceback.format_exc())
        res_log.info(f"Skipped {f}")
        skipped += 1
        continue

    file_count += 1
              
    proj_count += current_count
    proj_correct += current_correct

    if current_proj != last_proj:
        total_proj_count += 1
        proj_acc = round(last_proj_correct/last_proj_count, 8)
        res_log.info(f"{last_proj}: \t {last_proj_correct}/{last_proj_count} ({proj_acc})".expandtabs(100))
        res_log.info("-----------------")
        
        
    acc = round(current_correct/current_count, 8)
    res_log.info(f"{f}: \t {current_correct}/{current_count} ({acc})".expandtabs(100))
     
    last_proj = current_proj

acc = round(correct/total_count, 8)
res_log.info(f"Total: \t {correct}/{total_count} ({acc})".expandtabs(100))
res_log.info(f"Skipped {skipped} files.")

