import argparse, os, sys, json, torch
from datetime import datetime
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader

from agent import Agent
from helpers
from eval_env import FileEnv

''' arguments '''
parser = argparse.ArgumentParser()

# paths
parser.add_argument('--data', type=str, default='../data/')
parser.add_argument('--proof_steps', type=str, default='../proof_steps/')
parser.add_argument('--split', type=str, default='./jsons/split.json')
parser.add_argument('--tactics', type=str, default='./jsons/tactics.json')
parser.add_argument('--tactics_sorted', type=str, default='./jsons/tactics_sorted.json')
parser.add_argument('--generic_args', type=str, default='./jsons/generic_args.json')
parser.add_argument('--nonterminals', type=str, default='./jsons/nonterminals.json')

# run
parser.add_argument('--replay_batchsize', type=int, default=256)
parser.add_argument('--sl_batchsize', type=int, default=256)
parser.add_argument('--imitation', type=bool, default=False)
parser.add_argument('--episodes', type=int, default=1)

parser.add_argument('--proof_type', type=str, default='all')
parser.add_argument('--model_type', type=str, default='rl')

# proof search
parser.add_argument('--depth_limit', type=int, default=50)
parser.add_argument('--max_num_tacs', type=int, default=50)
parser.add_argument('--timeout', type=int, default=30)
parser.add_argument('--action_space', type=int, default=175)

# GNN
parser.add_argument('--embedding_dim', type=int, default=512)
parser.add_argument('--sortk', type=int, default=30)
parser.add_argument('--lr', type=float, default=1e-3)
parser.add_argument('--lr_sl', type=float, default=1e-3)
parser.add_argument('--dropout', type=float, default=0.5)

# rewards
parser.add_argument('--error_punishment', type=float, default=-1.0)
parser.add_argument('--neutral_reward', type=float, default=-0.25)
parser.add_argument('--success_reward', type=float, default=1)

# RL
parser.add_argument('--epsilon_start', type=float, default=1.0)
parser.add_argument('--epsilon_end', type=float, default=0.05)
parser.add_argument('--epsilon_decay', type=float, default=5e2)
parser.add_argument('--discount', type=float, default=0.5)


opts = parser.parse_args()
opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
opts.savepath = f"./models/{helpers.get_core_path(opts)}"

# loggers
run_log, res_log = helpers.setup_loggers(opts)
res_log.info(opts)



# agent
agent = Agent(opts)
res_log.info(agent.Q)
optimizer = torch.optim.RMSprop(agent.Q.parameters())
sl_optimizer = torch.optim.Adam(agent.Q.parameters(), lr=opts.lr_sl)

# dataset
train_files, valid_files, test_files = helpers.files_on_split(opts)
train_steps = helpers.get_files(opts, "train")
valid_steps = helpers.get_files(opts, "valid")
proof_steps = DataLoader(ProofStepData(train_steps + valid_steps), None, collate_fn=merge, num_workers=0)

