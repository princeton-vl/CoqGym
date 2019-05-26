(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib

type parenRelation = Notation_gram.parenRelation

val parenRelation_of_sexp : Sexp.t -> parenRelation
val sexp_of_parenRelation : parenRelation -> Sexp.t

type precedence = Notation_gram.precedence

val precedence_of_sexp : Sexp.t -> precedence
val sexp_of_precedence : precedence -> Sexp.t

type tolerability = Notation_gram.tolerability

val tolerability_of_sexp : Sexp.t -> tolerability
val sexp_of_tolerability : tolerability -> Sexp.t

type grammar_constr_prod_item = Notation_gram.grammar_constr_prod_item
val grammar_constr_prod_item_of_sexp : Sexp.t -> grammar_constr_prod_item
val sexp_of_grammar_constr_prod_item : grammar_constr_prod_item -> Sexp.t

type notation_grammar = Notation_gram.notation_grammar
val notation_grammar_of_sexp : Sexp.t -> notation_grammar
val sexp_of_notation_grammar : notation_grammar -> Sexp.t

