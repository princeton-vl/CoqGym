import argparse, os, sys, torch, json, traceback, gc
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

parser.add_argument("--num_tac_candidates", type=int, default=10)
parser.add_argument("--depth_limit", type=int, default=50)
parser.add_argument("--max_num_tacs", type=int, default=300)
parser.add_argument("--timeout", type=int, default=600)

parser.add_argument("--dropout", type=str, default=0.0)

parser.add_argument("--split2", type=int, default=1)

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

agent = SLAgent(opts, res_log)


_, _, test_files = eval_helpers.files_on_split(opts)
if opts.split2 == 1:
    test_files = test_files[0:125]


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
        total_proj_count += 1
        proj_acc = round(last_proj_correct/max(last_proj_count, 1), 6)
        res_log.info(f"{last_proj}: \t {last_proj_correct}/{last_proj_count} ({proj_acc})".expandtabs(80))
        acc = round(correct/total_count, 6)
        res_log.info(f"Current total: \t {correct}/{total_count} ({acc})".expandtabs(80))
        res_log.info(f"Skipped {skipped} files so far...")
        res_log.info("-----------------")
        
    current_count = 0
    current_correct = 0
    try:
        with FileEnv(f, max_num_tactics=opts.max_num_tacs, timeout=opts.timeout) as file_env:
            for proof_env in file_env:
                proof_name = proof_env.proof["name"]
                res, script = agent.prove(proof_env)

                total_count += 1
                current_count += 1
                if res:
                    current_correct += 1
                    correct += 1
                    
                run_log.info(f'{proof_name} -> {res}, {script}. Seen {total_count} ({round(total_count/13137, 4)} %) of proofs')
                gc.collect()
    except:
        run_log.info(traceback.format_exc())
        res_log.info(f"Skipped {f}")
        skipped += 1
        continue

    file_count += 1
    proj_count += current_count
    proj_correct += current_correct
        
    acc = round(current_correct/current_count, 6)
    res_log.info(f"{f}: \t {current_correct}/{current_count} ({acc})".expandtabs(80))
     
    last_proj = current_proj


acc = round(correct/total_count, 6)
res_log.info(f"Total: \t {correct}/{total_count} ({acc})".expandtabs(80))
res_log.info(f"Skipped {skipped} files.")

