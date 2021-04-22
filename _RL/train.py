import argparse, os, sys, json, torch
from datetime import datetime
sys.setrecursionlimit(100000)
sys.path.append(os.path.abspath('../'))

import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader

from agent import Agent
from helpers import setup_loggers, files_on_split, ProofStepData, merge, get_actions, is_equivalent, padd_context
from eval_env import FileEnv

proof_step_index = 0
def sl_train(dataloader):
    global proof_step_index
    count = 0
    for i, batch in enumerate(dataloader):
        if i < proof_step_index:
            continue
        if count >= opts.sl_batchsize:
            proof_step_index += count
            res_log.info(f'trained supervised learning on {count} proof steps')
            return

        for j in range(len(batch['goal'])):
            goal = batch['goal'][j]
            lc = batch['local_context'][j]
            gc = batch['env'][j]

            if opts.step_type == 'synthetic':
                if not batch['is_synthetic'][j]:
                    continue

            for c in gc:
                c['ident'] = c.pop('qualid')

            lc = padd_context(lc)
            gc = padd_context(gc)

            state = (goal, lc, gc)

            actions = get_actions(opts, state)
            tac = batch['tactic'][0]['text']

            valid_example = False
            for action in actions:
                if is_equivalent(opts, tac, action, state):
                    valid_example = True
                    tac = action

            if valid_example:
        
                label = torch.tensor(actions.index(tac))
                pred = agent.Q(state)

                loss = F.cross_entropy(pred.view(1, len(pred)), label.view(1))

                sl_optimizer.zero_grad()
                loss.backward()
                sl_optimizer.step()
        
                count += 1


def replay_train(replay_buffer):

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

    replay_stats = {opts.error_punishment: len([e for e in batch if e[2] == opts.error_punishment]), 
                    opts.neutral_reward: len([e for e in batch if e[2] == opts.neutral_reward]),
                    opts.success_reward: len([e for e in batch if e[2] == opts.success_reward])}
                    


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
parser.add_argument('--run', type=str, default='./logs/run_train.log')
parser.add_argument('--res', type=str, default='./logs/res_train.log')
parser.add_argument('--savepath', type=str, default='./models/Q')
parser.add_argument('--savepath_target', type=str, default='./models/target_Q')

# run
parser.add_argument('--epochs', type=int, default=100)
parser.add_argument('--replay_batchsize', type=int, default=256)
parser.add_argument('--sl_batchsize', type=int, default=256)
parser.add_argument('--imitation', type=bool, default=False)
parser.add_argument('--step_type', type=str, default='synthetic')
parser.add_argument('--episodes', type=int, default=1)

# proof search
parser.add_argument('--depth_limit', type=int, default=50)
parser.add_argument('--max_num_tacs', type=int, default=50)
parser.add_argument('--timeout', type=int, default=30)
parser.add_argument('--action_space', type=int, default=175)

# GNN
parser.add_argument('--embedding_dim', type=int, default=16)
parser.add_argument('--sortk', type=int, default=10)
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

# loggers
run_log, res_log = setup_loggers(opts)
res_log.info(opts)

# agent
agent = Agent(opts)
res_log.info(agent.Q)
optimizer = torch.optim.RMSprop(agent.Q.parameters())
sl_optimizer = torch.optim.Adam(agent.Q.parameters(), lr=opts.lr_sl)

# dataset
train_files, valid_files, test_files = files_on_split(opts)
proof_steps = DataLoader(ProofStepData(opts, "train"), 1, collate_fn=merge, num_workers=0)

# epochs
for n in range(opts.epochs):
    res_log.info(f'EPOCH: {n}')
    file_count = 0
    save_count = 0
    total_proofs_count = 0
    
    # proof files
    for f in train_files:
        agent.num_steps = 0
        agent.update_target_Q()
        
        if opts.imitation:
            sl_train(proof_steps)

        for i in range(opts.episodes):
            eps_start = agent.get_eps_tresh()
            error_count = 0
            skipped = 0
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
                    
                    try:
                        res = agent.train(proof_env)
                    except:
                        skipped += 1
                        continue

                    #print(res)

                    error_count += res['error_count']

                    total += 1
                    if res['res']:
                        num_correct += 1
                    
                    proof_count += 1

                    # replay expriences and supervised training
                    if len(agent.replay) >= opts.replay_batchsize:
                        replay_train(agent.replay)
                        agent.replay.clear()

                    total_proofs_count += 1
                    run_log.info(f'Seen {total_proofs_count/43844} % of proofs')
            
            acc = num_correct/max(total, 1)
            eps_end = agent.get_eps_tresh()
            res_log.info(f'{f}: \t {num_correct}/{total} ({acc})'.expandtabs(80))
            res_log.info(f'(episode {i}) eps: {eps_start} -> {eps_end}, errors: {error_count}, skipped: {skipped}\n')
            file_count += 1
        

        if file_count % 100 == 0:
            # save model
            torch.save({'state_dict': agent.Q.state_dict()},
                        f"{opts.savepath}%03d.pth" % save_count)

            torch.save({'state_dict': agent.Q.state_dict()},
                        f"{opts.savepath_target}%03d.pth" % save_count)
            save_count += 1
    
    # save final model
    torch.save({'state_dict': agent.Q.state_dict()},
                f"{opts.savepath}%03d.pth" % save_count)

    torch.save({'state_dict': agent.Q.state_dict()},
                f"{opts.savepath_target}%03d.pth" % save_count)
    save_count += 1
    
