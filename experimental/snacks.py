import argparse
import pickle
from glob import glob
import sys, os
sys.path.append(os.path.normpath(os.path.dirname(os.path.realpath(__file__))))
sys.path.append(
    os.path.normpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../"))
)
from gallina import traverse_postorder
from serapi import SerAPI

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
    
    print("-----------\n")
    print("Env:")
    for i, env in enumerate(proof_step['env']):
        print(env['qualid'])
    
    print("-----------\n")
    print("Local context:")
    for i, local_context in enumerate(proof_step['local_context']):
        print(local_context['text'])

    print("-----------\n")
    print("Goal:")
    print(proof_step['goal']['text'])

    print("-----------\n")
    print("Tactic:")
    print(proof_step['tactic']['text'])


    #print(proof_step['goal']['id'])
    #print(proof_step['goal']['text'])
    #print(proof_step['goal']['ast'].pretty())
    #print(proof_step['file'])
    #print(proof_step['tactic']['text'])
    #print(proof_step['tactic']['actions'])


def ser_api():
    serapi_parser = SerAPI(timeout=500)
    serapi_parser.send("(Add () \"Lemma addn0 n : n + 0 = n. Proof. now induction n. Qed.)\"")
    #print(serapi_parser.send("auto"))


if __name__ == "__main__":
    #print_asts()
    ser_api()
    