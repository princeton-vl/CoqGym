import argparse
import pickle
from glob import glob

def print_asts():
    arg_parser = argparse.ArgumentParser(
        description="Print Abstract Syntax Tree of a proof step"
    )
    arg_parser.add_argument(
        "--path", type=str, default="./proof_steps/train/00000000.pickle", help="path to proof step file"
    )
    args = arg_parser.parse_args()
    print(args)

    proof_path = args.path

    """
        step = {
            'file': STR,
            'proof_name': STR,
            'n_step': INT,
            'env': [{
                'qualid': STR,
                'ast': LARK.TREE.TREE,
            }]
            'local_context': [{
                'ident': STR,
                'text': STR
                'ast': LARK.TREE.TREE,
            }],
            'goal': {
                'id': STR,
                'text': STR,
                'ast: LARK.TREE.TREE,
            },
            'tactic_actions':  [INT|STR],
            'tactic_str': STR,
        }
    """
    proof_step = pickle.load(open(proof_path, "rb"))

    #print(proof_step['goal']['ast'].pretty())
    print(proof_step['file'])
    print(proof_step['tactic']['text'])
    print(proof_step['tactic']['actions'])

if __name__ == "__main__":
    print_asts()
    