#!/usr/bin/env python

import re
import sys

def main():
  infile = open(sys.argv[1], 'r')
  lines = infile.read()
  infile.close()

  # Delete proofs.
  proof_defined_pattern = \
    re.compile('\s*Proof.*?(Defined|Qed|Admitted)\.', re.DOTALL)
  lines = re.sub(proof_defined_pattern, lambda x: "", lines)

  # Mangle the 'Require Import' list.
  def import_fun(matchobj):
    return '''Require Import CoqListFacts.

Require Import AssocList.
Require Import MetatheoryAtom.
Import AtomSetImpl.'''
  lines = re.sub('Require Import CoqListFacts\.', import_fun, lines)

  # Module becomes Module Type.
  functor_pattern = \
    re.compile('Module Make.*?\n.*?\n.*?\.$', re.DOTALL | re.MULTILINE)
  lines = re.sub(functor_pattern, lambda x: "Module Type ENVIRONMENT.", lines)
  lines = re.sub('End Make.', lambda x: "End ENVIRONMENT.", lines)

  # Lemmas become Axioms.
  lines = re.sub('Lemma', lambda x: 'Axiom', lines)
  lines = re.sub('Theorem', lambda x: 'Axiom', lines)

  # Rename modules, types, and tactics.
  lines = re.sub('X\.t', lambda x: 'atom', lines)
  lines = re.sub('KeySet\.t', lambda x: 'atoms', lines)
  lines = re.sub('KeySet', lambda x: 'AtomSetImpl', lines)
  lines = re.sub('simpl_alist', lambda x: 'simpl_env', lines)
  lines = re.sub('rewrite_alist', lambda x: 'rewrite_env', lines)
  lines = re.sub('X\.eq_dec', lambda x: 'eq_atom_dec', lines)
  lines = re.sub('"alist"', lambda x: '"env"', lines)

  # Delete unneeded module instantiations.
  module_pattern = re.compile('^\s*Module [^T].*?\n', re.MULTILINE)
  lines = re.sub(module_pattern, lambda x: "", lines)

  # Done.
  print lines,
  print '''

(* ********************************************************************** *)
(** * Module instantiation *)

(** We can use our implementation of association lists (in AssocList) to
    implement a module with the above signature.   Note that the tactics
    provided end in [_env], not [_alist] as the implementation of
    [AssocList.Make] might suggest.  (Tactics do not need to agree between a
    module's signature and its implementation.) *)

Module Export EnvImpl : ENVIRONMENT := AssocList.Make AtomDT AtomSetImpl.'''

if __name__ == '__main__':
  main()
