# get a list of all tactics in CoqGym
# useful for testing the parser for tactics
import common
import sexpdata
from utils import iter_coq_files
import re
import argparse
import pdb
import sys
sys.setrecursionlimit(100000)

arg_parser = argparse.ArgumentParser(description='get a list of all tactics in CoqGym')
arg_parser.add_argument('--output', default='tactics.txt', type=str, help='the file to output')
args = arg_parser.parse_args()

tactics = set()

def collect_tacs(filename, file_data):
    tactics.update({cmd for cmd, vernac_type, _ in file_data['vernac_cmds'] if vernac_type == 'VernacExtend'})

iter_coq_files(common.data_root, collect_tacs)

oup = open(args.output, 'wt')
for t in tactics:
    oup.write(t + '\n')
print('output saved to ' + args.output)
