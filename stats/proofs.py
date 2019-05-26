# get the statistics of the proofs
import argparse
import common
from utils import iter_proofs
import pandas as pd
from collections import defaultdict
import numpy as np
import re
import pdb

arg_parser = argparse.ArgumentParser(description='get the statistics of the proofs')
arg_parser.add_argument('--synthetic', action='store_true')
arg_parser.add_argument('--output', default='proofs_statistics.csv', type=str, help='the csv file to output')
args = arg_parser.parse_args()

data = defaultdict(list)

def process_proof(filename, proof_data):
    if args.synthetic and 'goal_id' not in proof_data:
        return
    m = re.fullmatch(r'./data/(?P<project>[^/]+)/(?P<file>.+).json', filename)
    data['project'].append(m['project'])
    data['file'].append(m['file'] + '.v')
    data['name'].append(proof_data['name'])
    data['num_steps'].append(len(proof_data['steps']) - 1)  # not including the Qed at the end
    data['num_goals'].append(len(proof_data['goals']))
    data['num_env_constants'].append(len(proof_data['env']['constants']))
    data['num_env_inductives'].append(len(proof_data['env']['inductives']))
    data['num_env'].append(data['num_env_constants'][-1] + data['num_env_inductives'][-1])
    #data['num_env_constants_same_file'].append(len([const for const in proof_data['env']['constants'] 
    #                                                          if const['qualid'].startswith('SerTop.')]))
    data['avg_size_local_context'].append(np.mean([len(g['hypotheses']) for g in proof_data['goals'].values()]))

iter_proofs(common.data_root, process_proof, include_synthetic=args.synthetic, show_progress=True)
df = pd.DataFrame(data)
df.to_csv(args.output)
print('output saved to ', args.output)

# show some statistics
print(df.describe())
print(df.groupby('project').agg({'name': 'count', 
                                 'num_steps': 'mean', 
                                 'num_goals': 'mean',
                                 'num_env': 'mean'}))

