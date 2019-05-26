import common
import numpy as np
from utils import iter_proofs
from lark.exceptions import UnexpectedCharacters, ParseError
from tac_grammar import CFG, TreeBuilder, NonterminalNode, TerminalNode
import pdb


grammar = CFG(common.tac_grammar, 'tactic_expr')
tree_builder = TreeBuilder(grammar)

ast_height = []
num_tokens = []
num_chars = []
has_argument = []

def process_proof(filename, proof_data):
    global ast_height
    global num_tokens
    global num_chars

    for step in proof_data['steps']:
        if step['command'][1] != 'VernacExtend':
            continue
        if not step['command'][0].endswith('.'):
            continue
        tac_str = step['command'][0][:-1]

        try:
            tree = tree_builder.transform(grammar.parser.parse(tac_str))
        except (UnexpectedCharacters, ParseError) as ex:
            continue
        
        ast_height.append(tree.height())
        num_tokens.append(tree.num_tokens())
        num_chars.append(len(tac_str))
        has_argument.append(int(tree.has_argument()))

iter_proofs(common.data_root, process_proof, show_progress=True)
print(np.mean(ast_height), np.mean(num_tokens), np.mean(num_chars), np.mean(has_argument))
