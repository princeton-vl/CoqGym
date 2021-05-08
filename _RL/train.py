import argparse, os, sys, json, torch, traceback
import gc as garbage
from datetime import datetime
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader

from _RL.agent import Agent
import _RL.helpers as helpers
from eval_env import FileEnv


pos_memories = 0
neg_memories = 0
neutral_memories = 0
tot_replay_count = 0


def get_tactic_target(opts, tactics_json, tactic_app):
    tactic = get_tactic_true(tactic_app)            
    label = torch.tensor(tactics_json.index(tactic))         
    return label


def get_tactic_true(tactic_application):
    if tactic_application.startswith("simple induction"):
        return "simple induction"
    else:
        all_actions = tactic_application.split(" ")
        return all_actions[0]


proof_step_index = 0
def sl_train(dataloader):
    global proof_step_index
    count = 0
    for i, example in enumerate(dataloader):
        proof_step_index += 1
        if i < proof_step_index:
            continue
        if count >= opts.sl_batchsize:
            res_log.info(f'trained supervised learning on {count} {opts.proof_type} proof steps')
            return
        
        goal = example['goal']
        lc = example['local_context']
        gc = example['env'][j]
        state = (goal, lc, gc)
        tac = example['tactic']['text']
        label = get_tactic_target(tac)
        pred = agent.Q(state)
        loss = F.cross_entropy(pred.view(1, len(pred)), label.view(1))
        sl_optimizer.zero_grad()
        loss.backward()
        sl_optimizer.step()
        count += 1

    res_log.info(f'trained supervised learning on {count} {opts.proof_type} proof steps')

def replay_train(replay_buffer):
    global pos_memories
    global neg_memories
    global neutral_memories
    global tot_replay_count

    batch = replay_buffer.sample(opts.replay_batchsize)
    q_batch = torch.tensor([b[0] for b in batch], requires_grad=True)
    _q_batch = torch.tensor([b[1] for b in batch])
    r_batch = torch.tensor([b[2] for b in batch])
    # add discount and reward
    targets = (_q_batch * opts.discount) + r_batch
    # Compute Huber loss
    loss = F.smooth_l1_loss(q_batch, targets)
    # Optimize the agent's Q
    optimizer.zero_grad()
    loss.backward()
    '''
    for param in agent.Q.parameters():
        print(param.size())
        param.grad.data.clamp_(-1, 1)
    '''
    optimizer.step()
    
    pos_memories += list(r_batch).count(1)
    neg_memories += list(r_batch).count(-1)
    neutral_memories += list(r_batch).count(0)
    tot_replay_count += len(batch)
    

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
parser.add_argument('--replay_batchsize', type=int, default=32)
parser.add_argument('--sl_batchsize', type=int, default=256)
parser.add_argument('--episodes', type=int, default=1)

parser.add_argument('--proof_type', type=str, default='synthetic')
parser.add_argument('--model_type', type=str, default='rl')

# proof search
parser.add_argument('--depth_limit', type=int, default=50)
parser.add_argument('--max_num_tacs', type=int, default=50)
parser.add_argument('--timeout', type=int, default=3)
parser.add_argument('--action_space', type=int, default=49)

# GNN
parser.add_argument('--embedding_dim', type=int, default=256)
parser.add_argument('--sortk', type=int, default=30)
parser.add_argument('--lr', type=float, default=1e-3)
parser.add_argument('--lr_sl', type=float, default=1e-3)
parser.add_argument('--l2', type=float, default=5e-6)
parser.add_argument('--dropout', type=float, default=0.7)

# rewards
parser.add_argument('--error_punishment', type=float, default=-1.0)
parser.add_argument('--neutral_reward', type=float, default=0)
parser.add_argument('--success_reward', type=float, default=1)

# RL
parser.add_argument('--epsilon_start', type=float, default=1.0)
parser.add_argument('--epsilon_end', type=float, default=0.1)
parser.add_argument('--epsilon_decay', type=float, default=8e4)
parser.add_argument('--discount', type=float, default=0.5)


opts = parser.parse_args()
opts.device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
opts.savepath = f"./models/{helpers.get_core_path(opts)}"
if opts.episodes > 1:
    opts.epsilon_decay = 2e1

# loggers
run_log, res_log = helpers.setup_loggers(opts)
res_log.info(opts)


# agent
agent = Agent(opts)
res_log.info(agent.Q)
optimizer = torch.optim.RMSprop(agent.Q.parameters(), weight_decay=opts.l2)
sl_optimizer = torch.optim.Adam(agent.Q.parameters(), lr=opts.lr_sl, weight_decay=opts.l2)

# dataset
train_files, _, _ = helpers.files_on_split(opts)

if 'im' in opts.model_type: 
    train_steps = helpers.get_files(opts, "train", run_log)
    proof_steps = DataLoader(helpers.ProofStepData(train_steps), None, num_workers=0)



save_count = 0
skipped = 0
total = 0
last_hundred = []
for f in train_files:
    res_log.info('')

    if opts.model_type == 'im':
        sl_train(proof_steps)

    if opts.episodes > 1:
        agent.num_steps = 0

    for n in range(opts.episodes):
        
        res_log.info(f'Episode: {n}')
        correct = 0
        count = 0
        eps_start = agent.get_eps_tresh()

        try:
            with FileEnv(f, max_num_tactics=opts.max_num_tacs, timeout=opts.timeout) as file_env:
                for proof_env in file_env:
                    name = proof_env.proof['name'] 

                    res = agent.train(proof_env)
                    run_log.info(res)
                    count += 1
                    total += 1
                    agent.num_steps += 1
                    garbage.collect()
                    if res['res']:
                        if len(last_hundred) < 1000:
                            last_hundred.append(1)
                        else:
                            last_hundred = last_hundred[1:]
                            last_hundred.append(1)
                        correct += 1
                    else:
                        if len(last_hundred) < 1000:
                            last_hundred.append(0)
                        else:
                            last_hundred = last_hundred[1:]
                            last_hundred.append(0)

                    if len(agent.replay) >= opts.replay_batchsize:
                        replay_train(agent.replay)
                        agent.replay.clear()
                    
                    if total % 1000 == 0:
                        agent.update_target_Q()

                    run_log.info(f'Seen {total} ({round(total/(57719), 8)} %) of proofs')
            
            acc = round(correct/max(count, 1), 8)
            eps_end = agent.get_eps_tresh()
            res_log.info(f'{f}: \t {correct}/{count} ({acc})'.expandtabs(80))
            res_log.info(f'replayed {tot_replay_count} memories -> pos: {pos_memories}, neg: {neg_memories}, neutral: {neutral_memories}')
            pos_memories = 0
            neg_memories = 0
            neutral_memories = 0
            tot_replay_count = 0
            if len(last_hundred) == 1000:
                res_log.info(f'eps: {eps_start} -> {eps_end}, trail: {sum(last_hundred)}')
            else:
                res_log.info(f'eps: {eps_start} -> {eps_end}, trail: N/A')
            
        except KeyboardInterrupt:
            exit()
        except Exception as e:
            skipped += 1
            traceback.print_exc()
            res_log.info(f'skipped {f}')
            continue
    
    if total > 57719:
        res_log.info("Reached 57,719 proofs, ending it here.")
        break
    

torch.save({'state_dict': agent.Q.state_dict()}, f"{opts.savepath}_q.pth")


