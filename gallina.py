# Utilities for reconstructing Gallina terms from their serialized S-expressions in CoqGym
from io import StringIO
from vernac_types import Constr__constr
from lark import Lark, Transformer, Visitor, Discard
from lark.lexer import Token
from lark.tree import Tree
from lark.tree import pydot__tree_to_png
import logging
logging.basicConfig(level=logging.DEBUG)
from collections import defaultdict
import re
import pdb


def traverse_postorder(node, callback):
    for c in node.children:
        if isinstance(c, Tree):
            traverse_postorder(c, callback)
    callback(node)


class GallinaTermParser:

    def __init__(self, caching=True):
        self.caching = caching
        t = Constr__constr()
        self.grammar = t.to_ebnf(recursive=True) + '''
        %import common.STRING_INNER
        %import common.ESCAPED_STRING
        %import common.SIGNED_INT
        %import common.WS
        %ignore WS
        '''
        self.parser = Lark(StringIO(self.grammar), start='constr__constr', parser='lalr')
        if caching:
            self.cache = {}


    def parse_no_cache(self, term_str):
        ast = self.parser.parse(term_str)

        ast.quantified_idents = set()

        def get_quantified_idents(node):
            if node.data == 'constructor_prod' and node.children != [] and node.children[0].data == 'constructor_name':
                ident = node.children[0].children[0].value
                if ident.startswith('"') and ident.endswith('"'):
                    ident = ident[1:-1]
                ast.quantified_idents.add(ident)

        traverse_postorder(ast, get_quantified_idents)
        ast.quantified_idents = list(ast.quantified_idents)

        def compute_height_remove_toekn(node):
            children = []
            node.height = 0
            for c in node.children:
                if isinstance(c, Tree):
                    node.height = max(node.height, c.height + 1)
                    children.append(c)
            node.children = children

        traverse_postorder(ast, compute_height_remove_toekn)
        return ast


    def parse(self, term_str):
        if self.caching:
            if term_str not in self.cache:
                self.cache[term_str] = self.parse_no_cache(term_str)
            return self.cache[term_str]
        else:
            return self.parse_no_cache(term_str)


    def print_grammar(self):
        print(self.grammar)    


class Counter(Visitor):

    def __init__(self):
        super().__init__()
        self.counts_nonterminal = defaultdict(int)
        self.counts_terminal = defaultdict(int)

    def __default__(self, tree):
         self.counts_nonterminal[tree.data] += 1
         for c in tree.children:
             if isinstance(c, Token):
                 self.counts_terminal[c.value] += 1


class TreeHeight(Transformer):

    def __default__(self, symbol, children, meta):
        return 1 + max([0 if isinstance(c, Token) else c for c in children] + [-1])


class TreeNumTokens(Transformer):

    def __default__(self, symbol, children, meta):
        return sum([1 if isinstance(c, Token) else c for c in children])

