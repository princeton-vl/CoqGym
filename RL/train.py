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


def validate():
    res_log.info('-----VALIDATION----')
    total_count = 0
    file_count = 0
    proj_count = 0
    total_proj_count = 0
    skipped = 0
    correct = 0
    proj_correct = 0
    last_proj = valid_files[0].split("/")[2]
    for f in valid_files:
        current_proj = f.split("/")[2]
        if current_proj != last_proj:
            last_proj_count = proj_count
            last_proj_correct = proj_correct
            proj_count = 0
            proj_correct = 0    
        
        current_count = 0
        current_correct = 0
        try:
            with FileEnv(f, max_num_tactics=300, timeout=30) as file_env:
                for proof_env in file_env:
                    proof_name = proof_env.proof["name"]
                    #print(proof_name)
                    res = agent.test(proof_env)
                    total_count += 1
                    current_count += 1
            
                    if res["proved"]:
                        current_correct += 1
                        correct += 1

        except:
            res_log.info(f"Skipped {f}")
            skipped += 1
            continue
                            
        file_count += 1
              
        proj_count += current_count
        proj_correct += current_correct

        if current_proj != last_proj:
            total_proj_count += 1
            proj_acc = last_proj_correct/last_proj_count
            res_log.info(f"{last_proj}: \t {last_proj_correct}/{last_proj_count} ({proj_acc})".expandtabs(100))
            res_log.info("-----------------")
        
        
        acc = current_correct/current_count
        res_log.info(f"{f}: \t {current_correct}/{current_count} ({acc})".expandtabs(100))
        run_log.info(file_count/len(test_files))
        
        last_proj = current_proj
    
    acc = correct/total_count
    res_log.info(f"Total: \t {correct}/{total_count} ({acc})".expandtabs(100))
    res_log.info(f"Skipped {skipped} files.")
    res_log.info('-----VALIDATION END----')

proof_step_index = 0
def sl_train(dataloader):
    global proof_step_index
    count = 0
    for i, batch in enumerate(dataloader):
        if i < proof_step_index:
            continue
        if count >= opts.sl_batchsize:
            proof_step_index += count
            res_log.info(f'trained supervised learning on {count} {opts.step_type} proof steps')
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
            tac = batch['tactic'][j]['text']

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
    res_log.info(f'trained supervised learning on {count} {opts.step_type} proof steps')


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
parser.add_argument('--step_type', type=str, default='')
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

    validate()
    
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
            try:
                with FileEnv(f, max_num_tactics=opts.max_num_tacs, timeout=opts.timeout) as file_env:
                
                    proof_count = 0
                    # ProofEnv in FileEnv
                    for proof_env in file_env:
                        ''' train agent on current ProofEnv '''
                        name = proof_env.proof['name']
                        human_proof = [step['command'][0] for step in proof_env.proof['steps']]
                    
                        res = agent.train(proof_env)
      
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
                        run_log.info(f'Seen {total_proofs_count} ({total_proofs_count/43844} %) of proofs')
            
                acc = num_correct/max(total, 1)
                eps_end = agent.get_eps_tresh()
                res_log.info(f'{f}: \t {num_correct}/{total} ({acc})'.expandtabs(80))
                res_log.info(f'(episode {i}) eps: {eps_start} -> {eps_end}, errors: {error_count}, skipped: {skipped}\n')
                file_count += 1

            except:
                skipped += 1
                res_log.info(f'skipped {f}')
                continue
        

        if file_count % 10000 == 0:
            # save model
            torch.save({'state_dict': agent.Q.state_dict()},
                        f"{opts.savepath}%03d.pth" % save_count)

            torch.save({'state_dict': agent.Q.state_dict()},
                        f"{opts.savepath_target}%03d.pth" % save_count)
            save_count += 1

            validate()
            

    
    # save final model
    torch.save({'state_dict': agent.Q.state_dict()},
                f"{opts.savepath}%03d.pth" % save_count)

    torch.save({'state_dict': agent.Q.state_dict()},
                f"{opts.savepath_target}%03d.pth" % save_count)
    save_count += 1
    
