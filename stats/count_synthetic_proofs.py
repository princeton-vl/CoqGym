import common
from utils import iter_proofs
from collections import defaultdict
import pdb

cnt = defaultdict(int)

def count_proof(filename, proof_data):
    global cnt
    if 'goal_id' not in proof_data:
        return
    cnt[proof_data['length']] += 1

iter_proofs(common.data_root, count_proof, include_synthetic=True, show_progress=True)
print('')
print(cnt)
