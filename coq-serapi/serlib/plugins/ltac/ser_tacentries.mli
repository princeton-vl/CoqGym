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
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Ltac_plugin

type 'a grammar_tactic_prod_item_expr = 'a Tacentries.grammar_tactic_prod_item_expr
val grammar_tactic_prod_item_expr_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a grammar_tactic_prod_item_expr
val sexp_of_grammar_tactic_prod_item_expr : ('a -> Sexp.t) -> 'a grammar_tactic_prod_item_expr -> Sexp.t

type raw_argument = Tacentries.raw_argument
val raw_argument_of_sexp : Sexp.t -> raw_argument
val sexp_of_raw_argument : raw_argument -> Sexp.t
