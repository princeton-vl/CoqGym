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

type hint_db_name = Hints.hint_db_name

val sexp_of_hint_db_name : hint_db_name -> Sexp.t
val hint_db_name_of_sexp : Sexp.t -> hint_db_name

type 'a hints_path_gen = 'a Hints.hints_path_gen

val sexp_of_hints_path_gen : ('a -> Sexp.t) -> 'a hints_path_gen -> Sexp.t
val hints_path_gen_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a hints_path_gen

type 'a hints_path_atom_gen = 'a Hints.hints_path_atom_gen

val sexp_of_hints_path_atom_gen : ('a -> Sexp.t) -> 'a hints_path_atom_gen -> Sexp.t
val hints_path_atom_gen_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a hints_path_atom_gen

type hints_path = Hints.hints_path

val sexp_of_hints_path : hints_path -> Sexp.t
val hints_path_of_sexp : Sexp.t -> hints_path

type reference_or_constr = Hints.reference_or_constr
val reference_or_constr_of_sexp : Sexp.t -> reference_or_constr
val sexp_of_reference_or_constr : reference_or_constr -> Sexp.t

type hint_info_expr = Hints.hint_info_expr
val hint_info_expr_of_sexp : Sexp.t -> hint_info_expr
val sexp_of_hint_info_expr : hint_info_expr -> Sexp.t

type hint_mode = Hints.hint_mode
val hint_mode_of_sexp : Sexp.t -> hint_mode
val sexp_of_hint_mode : hint_mode -> Sexp.t

type hints_expr = Hints.hints_expr
val hints_expr_of_sexp : Sexp.t -> hints_expr
val sexp_of_hints_expr : hints_expr -> Sexp.t
