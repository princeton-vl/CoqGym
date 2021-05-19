import argparse, os, sys, torch, json, traceback, gc
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import eval_helpers
from eval_env import FileEnv

from rl_agent import RLAgent
from sl_agent import SLAgent

from torch.multiprocessing import Pool, Process, set_start_method
import multiprocessing
import logging
from logging.handlers import QueueHandler, QueueListener
import time
import random

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
parser.add_argument("--split2", type=int, default=0)
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

agent = SLAgent(opts)


def go(f):
    #logging.info(f)
    global agent
    count = 0
    correct = 0
    skipped = 0
    try:
        with FileEnv(f, max_num_tactics=300, timeout=600) as file_env:
            for proof_env in file_env:
                proof_name = proof_env.proof["name"]
                res, script = agent.prove(proof_env)

                count += 1
                if res:
                    correct += 1
                    
                gc.collect()

                #run_log.info(f'{proof_name} -> {res}, {script}. Seen {total_count} ({round(total_count/13137, 4)} %) of proofs')
    except:
        #run_log.info(traceback.format_exc())
        #res_log.info(f"Skipped {f}")
        skipped += 1

    logging.info(f"{f}: \t {correct}/{count}".expandtabs(80))

    return {f:[count, correct, skipped]}

def worker_init(q):
    # all records from worker processes go to qh and then into q
    qh = QueueHandler(q)
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)
    logger.addHandler(qh)


def logger_init():
    core = eval_helpers.get_core_path(opts)
    path = f"./logs/{core}res.log"
    try:
        os.remove(path)
    except:
        pass

    q = multiprocessing.Queue()
    # this is the handler for all log records
    handler = logging.FileHandler(path)
    handler.setFormatter(logging.Formatter("%(asctime)s:\t%(message)s"))

    # ql gets records from the queue and sends them to the handler
    ql = QueueListener(q, handler)
    ql.start()

    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)
    # add the handler to the logger so records from this process are handled
    logger.addHandler(handler)

    return ql, q

if __name__ == '__main__':
    total_count = 0
    total_skipped = 0
    total_correct = 0
    proj_correct = {}

    try:
     set_start_method('spawn')
    except RuntimeError:
        pass

    _, _, test_files = eval_helpers.files_on_split(opts)
    if opts.split2 == 1:
        test_files = test_files[0:125]
    elif opts.split2 == 2:
        test_files = test_files[125:300]
    elif opts.split2 == 3:
        test_files = test_files[300:488]
    elif opts.split2 == 4:
        test_files = test_files[488:]
    
    q_listener, q = logger_init()
    pool = Pool(16, worker_init, [q])
    res = pool.map(go, test_files)
    pool.close()
    pool.join()
    q_listener.stop()
    logging.info(res)

