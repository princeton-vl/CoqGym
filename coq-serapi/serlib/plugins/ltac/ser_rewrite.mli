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

type unary_strategy = Rewrite.unary_strategy
val unary_strategy_of_sexp : Sexp.t -> unary_strategy
val sexp_of_unary_strategy : unary_strategy -> Sexp.t

type binary_strategy = Rewrite.binary_strategy
val binary_strategy_of_sexp : Sexp.t -> binary_strategy
val sexp_of_binary_strategy : binary_strategy -> Sexp.t

type ('a,'b) strategy_ast = ('a,'b) Rewrite.strategy_ast

val strategy_ast_of_sexp : (Sexp.t -> 'a) -> (Sexp.t -> 'b) -> Sexp.t -> ('a,'b) strategy_ast
val sexp_of_strategy_ast : ('a -> Sexp.t) -> ('b -> Sexp.t) -> ('a,'b) strategy_ast -> Sexp.t
