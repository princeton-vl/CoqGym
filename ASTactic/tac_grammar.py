from glob import glob
import re
from io import StringIO
from lark import Lark, Transformer
from lark.lexer import Token
import logging
logging.basicConfig(level=logging.DEBUG)
import pdb
from progressbar import ProgressBar
import sys


class RuleBuilder(Transformer):

    def symbol(self, children):
        assert len(children) == 1
        if children[0].type == 'TERMINAL':
            assert children[0].value.isupper()
            return children[0].value
        elif children[0].type == 'NONTERMINAL':
            assert children[0].value.islower()
            return children[0].value
        else:
            assert children[0].type in ['ESCAPED_STRING', 'REGEXP']
            return children[0].value


    def rhs(self, children):
        return children 


    def nonterminal_rule(self, children):
        assert children[0].type == 'NONTERMINAL'
        return [(children[0].value, c) for c in children[1:]]


    def terminal_rule(self, children):
        assert children[0].type == 'TERMINAL'
        return [(children[0].value, children[1].value)]


    def rule(self, children):
        assert len(children) == 1
        return children[0]


class CFG:

    def __init__(self, grammar_file, start_symbol):
        self.terminal_symbols = []
        self.nonterminal_symbols = []
        self.production_rules = []
        self.start_symbol = start_symbol

        meta_grammar = '''
            rule : nonterminal_rule
                 | terminal_rule
            nonterminal_rule : "!"? NONTERMINAL ":" rhs ("|" rhs)*
            NONTERMINAL : /[a-z0-9_]+/
            ALIAS : /[a-z_]+/
            symbol : TERMINAL
                   | NONTERMINAL
                   | ESCAPED_STRING
                   | REGEXP
            rhs : symbol* ["->" ALIAS]
            terminal_rule : TERMINAL ":" ESCAPED_STRING
                          | TERMINAL ":" REGEXP
            TERMINAL : /[A-Z_]+/
            REGEXP : "/" STRING_INNER+ "/"
            %import common.STRING_INNER
            %import common.ESCAPED_STRING
            %import common.WS
            %ignore WS
        '''
        meta_parser = Lark(meta_grammar, start='rule', parser='earley')
        t = RuleBuilder()
        self.ebnf = open(grammar_file).read()

        for rule_ebnf in self.ebnf.split('\n\n'):
            if rule_ebnf.startswith('%'):
                continue
            rules = t.transform(meta_parser.parse(rule_ebnf))
            if rules[0][0].islower():
                self.nonterminal_symbols.append(rules[0][0])
                self.production_rules.extend(rules)
            else:
                self.terminal_symbols.append(rules[0][0])
        self.symbols = self.nonterminal_symbols + self.terminal_symbols


        self.parser = Lark(StringIO(self.ebnf), start=self.start_symbol, parser='earley', debug=True)


    def get_applicable_rules(self, symbol):
        return [i for i, rule in enumerate(self.production_rules) if rule[0] == symbol]


    def __str__(self):
        return self.ebnf


class Node:

    def __init__(self, symbol, parent):
        self.symbol = symbol
        self.parent = parent
        self.pred = None  # predecessor in depth-first search
        self.state = None  # the hidden state of GRU
        self.action = None  # the production rule used to expand this node


class NonterminalNode(Node):

    def __init__(self, symbol, parent):
        super().__init__(symbol, parent)
        self.children = []


    def __str__(self):
        return 'NonterminalNode(%s, children=%s)' % (self.symbol, str(self.children))


    def __repr__(self):
        return str(self)


    def expand(self, rule):
        assert rule[0] == self.symbol and self.action is None and self.children == []
        self.action = rule
        for entry in rule[1]:
            if entry.startswith('"') and entry.endswith('"'):  # token
                 self.children.append(Token('literal', entry[1:-1]))
            elif entry.islower():  # nonterminal symbol
                self.children.append(NonterminalNode(entry, self))
            else:  # terminal symbol
                assert entry.isupper()
                self.children.append(TerminalNode(entry, self))


    def to_tokens(self):
        assert self.action is not None
        fields = []
        for r, c in zip(self.action[1], self.children):
            if isinstance(c, Token):
                assert c.value == r[1:-1]
                fields.append(c.value)
            elif isinstance(c, NonterminalNode):
                assert c.symbol == r
                fields.append(c.to_tokens())
            else:
                assert isinstance(c, TerminalNode)
                fields.append(c.token)
        return ' '.join(fields).strip()


    def traverse_pre(self, callback):
        callback(self)
        for c in self.children:
            if isinstance(c, Node):
                c.traverse_pre(callback)


    def height(self):
        return 1 + max([-1] + [0 if isinstance(c, Token) else c.height() for c in self.children])

    
    def num_tokens(self):
        n = 0
        for c in self.children:
            if isinstance(c, Token) or isinstance(c, TerminalNode):
                n += 1
            else:
                assert isinstance(c, NonterminalNode)
                n += c.num_tokens()
        return n

    def has_argument(self):
        result = False
        for c in self.children:
            if isinstance(c, TerminalNode):
                return True
            if isinstance(c, NonterminalNode):
                result = result or c.has_argument()
        return result


class TerminalNode(Node):

    def __init__(self, symbol, parent):
        super().__init__(symbol, parent)
        self.action = symbol
        self.token = None


    def expand(self, token):
        self.token = token


    def __str__(self):
        return 'TerminalNode(%s, token=%s)' % (self.symbol, str(self.action))


    def __repr__(self):
        return str(self)


    def traverse_pre(self, callback):
        callback(self)


    def height(self):
        return 0


def find_rule(symbol, children, production_rules):
    matches = []
    for rule in production_rules:
        if rule[0] != symbol:
            continue
        if len(rule[1]) != len(children):
            continue
        for r, c in zip(rule[1], children):
            if isinstance(c, Token):
                if not isinstance(r, str):
                    break
                if not (r.startswith('"') and r.endswith('"')):
                    break
                if c.value != r[1:-1]:
                    break
            elif isinstance(c, TerminalNode):
                if not r.isupper() or r != c.symbol:
                    break
            elif isinstance(c, NonterminalNode):
                if not r.islower() or r != c.symbol:
                    break
            else:
                raise TypeError
        else:
            matches.append(rule)
    assert len(matches) == 1
    return matches[0]


class TreeBuilder(Transformer):

    def __init__(self, grammar):
        super().__init__()
        self.grammar = grammar


    def __default__(self, symbol, children, meta):
        node = NonterminalNode(symbol, parent=None)

        for c in children:
            if isinstance(c, Token):
                if c.type in self.grammar.terminal_symbols:
                    t = TerminalNode(c.type, parent=None)
                    t.token = c.value
                    c = t
            else:
                assert isinstance(c, NonterminalNode) and c.parent is None
                c.parent = node
            node.children.append(c)

        node.action = find_rule(symbol, node.children, self.grammar.production_rules)
        return node


if __name__ == '__main__':
    grammar = CFG('tactics.ebnf', 'tactic_expr')
    print(grammar)

    oup = open('fails.txt', 'wt')
    num_failed = 0
    num_succeeded = 0

    for tac_str in open('correct_tacs.txt'):
        tac_str = tac_str.strip()
        #assert tac_str.endswith('.')
        #tac_str = tac_str[:-1]
        try:
            tree = grammar.parser.parse(tac_str)
            pdb.set_trace()
            num_succeeded += 1
        except Exception as ex:
            oup.write(tac_str + '\n')
            num_failed += 1

    print(num_succeeded, num_failed)

