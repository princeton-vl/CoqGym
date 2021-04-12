import argparse, os, sys, json, torch
from datetime import datetime
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import torch.nn as nn

from agent import Agent
from helpers import setup_loggers, files_on_split
from eval_env import FileEnv

''' arguments '''
parser = argparse.ArgumentParser()

# paths
parser.add_argument('--data', type=str, default='../data/')
parser.add_argument('--split', type=str, default='./jsons/split.json')
parser.add_argument('--tactics', type=str, default='./jsons/tactics.json')
parser.add_argument('--tactics_sorted', type=str, default='./jsons/tactics_sorted.json')
parser.add_argument('--generic_args', type=str, default='./jsons/generic_args.json')
parser.add_argument('--nonterminals', type=str, default='./jsons/nonterminals.json')
parser.add_argument('--run', type=str, default='./logs/run_train.log')
parser.add_argument('--res', type=str, default='./logs/res_train.log')

# run
parser.add_argument('--epochs', type=int, default=1)
parser.add_argument('--episodes', type=int, default=100)

# proof search
parser.add_argument('--depth_limit', type=int, default=50)
parser.add_argument('--max_num_tacs', type=int, default=10)
parser.add_argument('--timeout', type=int, default=600)
parser.add_argument('--action_space', type=int, default=175)

# GNN and RL
parser.add_argument('--embedding_dim', type=int, default=128)
parser.add_argument('--sortk', type=int, default=10)
parser.add_argument('--lr', type=float, default=1e-1)
parser.add_argument('--dropout', type=float, default=0.1)
parser.add_argument('--reward', type=float, default=1)
#parser.add_argument('--punishment', type=float, default=-1)
parser.add_argument('--epsilon_start', type=float, default=0.7)
parser.add_argument('--epsilon_end', type=float, default=0.05)
parser.add_argument('--epsilon_decay', type=float, default=1e3)
parser.add_argument('--discount', type=float, default=0.9)
parser.add_argument('--eligibility', type=float, default=0.5)

opts = parser.parse_args()
opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

# loggers
run_log, res_log = setup_loggers(opts)

# dataset
train_files, valid_files, test_files = files_on_split(opts)
train_files = test_files

# agent
agent = Agent(opts)
res_log.info(agent.q_function)
#optimizer = torch.optim.Adam(agent.policy.parameters(), lr=opts.lr)
#criterion = nn.MSELoss()

# epochs
for n in range(opts.epochs):
    # proof files
    for f in train_files:
        for i in range(opts.episodes):

            num_correct = 0
            total = 0
            # load FileEnv
            with FileEnv(f, max_num_tactics=opts.max_num_tacs, timeout=opts.timeout) as file_env:
                
                proof_count = 0
                # ProofEnv in FileEnv
                for proof_env in file_env:
                    ''' train agent on current ProofEnv '''
                    name = proof_env.proof['name']
                    human_proof = [step['command'][0] for step in proof_env.proof['steps']]
                    run_log.info(f"name: {name}")
                    run_log.info(f"human proof: {human_proof}")

                    res = agent.train(proof_env)

                    #print(f"{res['res']}, {res['script']}")
                    print(f"{name}: {res}\n")

                    #expected_rewards = torch.tensor(res['expected_rewards'], requires_grad=True)
                    #true_reward = torch.tensor([res['reward']]*len(expected_rewards))
                    #loss = criterion(expected_rewards, true_reward)
                    #print(loss)
                    #optimizer.zero_grad()
                    #loss.backward()
                    #optimizer.step()

                    
                    total += 1
                    if res['res']:
                        num_correct += 1
                    
                    proof_count += 1
                    if proof_count > 0:
                        break
            acc = num_correct/total
            res_log.info(f"{f}: \t {num_correct}/{total} ({acc})".expandtabs(80))
        break

