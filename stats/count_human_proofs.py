import os
import common
from utils import iter_proofs
from collections import defaultdict
import json
import pdb

projs_split = json.load(open('projs_split.json'))
cnt = defaultdict(int)
cnt_projs = defaultdict(int)

def count_proof(filename, proof_data):
    global cnt
    global cnt_projs
    proj = filename.split(os.path.sep)[2]
    if proj in projs_split['projs_train']:
        split = 'train'
    elif proj in projs_split['projs_valid']:
        split = 'valid'
    else:
        split = 'test'
    cnt[split] += 1
    cnt_projs[proj] += 1

iter_proofs(common.data_root, count_proof, include_synthetic=False, show_progress=True)
print('')
print(cnt)
print(cnt_projs)
