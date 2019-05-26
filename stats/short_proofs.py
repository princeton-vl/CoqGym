# get the statistics of the proofs
import argparse
import common
from utils import iter_proofs
import pandas as pd
import numpy as np
import re
import pdb

oup = open('short_proofs.txt', 'wt')

def process_proof(filename, proof_data):
    if 1 <= len(proof_data['steps']) <= 2:
        print(proof_data['steps'][0]['command'][0])
        oup.write(proof_data['steps'][0]['command'][0] + '\n')

iter_proofs(common.data_root, process_proof)

