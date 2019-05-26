(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type 'a red_atom = 'a Genredexpr.red_atom

val red_atom_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a red_atom
val sexp_of_red_atom : ('a -> Sexp.t) -> 'a red_atom -> Sexp.t

type 'a glob_red_flag =  'a Genredexpr.glob_red_flag

val glob_red_flag_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a glob_red_flag
val sexp_of_glob_red_flag : ('a -> Sexp.t) -> 'a glob_red_flag -> Sexp.t

type ('a, 'b, 'c) red_expr_gen =  ('a, 'b, 'c) Genredexpr.red_expr_gen

val red_expr_gen_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) ->
  (Sexp.t -> 'c) -> Sexp.t -> ('a, 'b, 'c) red_expr_gen
val sexp_of_red_expr_gen :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) ->
  ('c -> Sexp.t) -> ('a, 'b, 'c) red_expr_gen -> Sexp.t

type ('a, 'b, 'c) may_eval =  ('a, 'b, 'c) Genredexpr.may_eval
val may_eval_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) ->
  (Sexp.t -> 'c) -> Sexp.t -> ('a, 'b, 'c) may_eval
val sexp_of_may_eval :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) ->
  ('c -> Sexp.t) -> ('a, 'b, 'c) may_eval -> Sexp.t

type raw_red_expr = Genredexpr.raw_red_expr
val raw_red_expr_of_sexp : Sexp.t -> raw_red_expr
val sexp_of_raw_red_expr : raw_red_expr -> Sexp.t
