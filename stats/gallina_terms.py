# get a list of all Gallina terms in CoqGym
# useful for testing the parser for Gallina terms
import common
import lmdb
import sexpdata
from utils import iter_sexp_cache
import re
import argparse
import pdb
import sys

arg_parser = argparse.ArgumentParser(description='get a list of all Gallina terms in CoqGym')
arg_parser.add_argument('--output', default='gallina_terms.txt', type=str, help='the file to output')
args = arg_parser.parse_args()

terms = set()

def save():
    oup = open(args.output, 'wt')
    for t in terms:
        oup.write(t + '\n')
    print('output saved to ' + args.output)

def collect_terms(i, key, sexp_str):
    if i % 10000 == 1:
        save()
    sys.setrecursionlimit(1000000)
    if sexp_str.startswith('(CoqAst'):  # Coq command
        return

    if re.match('\(\(name \d+\) \(ty', sexp_str):  # goal
        goal = sexpdata.loads(sexp_str, nil=None, true=None)
        type = sexpdata.dumps(goal[1][1])
        terms.add(type)
        for hyp in goal[2][1]:
          hypothesis = sexpdata.dumps(hyp[2])
          terms.add(hypothesis)

    if sexp_str.startswith('((Constant'):  # constant
        constant = sexpdata.loads(sexp_str, nil=None, true=None)
        type = sexpdata.dumps(constant[1][0][2][1])
        terms.add(type)

    if sexp_str.startswith('((Mutind'):  # inductive
        return

iter_sexp_cache(common.db_path, collect_terms)
save()
