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

type 'a or_var = 'a Locus.or_var
val or_var_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a or_var
val sexp_of_or_var : ('a -> Sexp.t) -> 'a or_var -> Sexp.t

type 'a occurrences_gen = 'a Locus.occurrences_gen
val occurrences_gen_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a occurrences_gen
val sexp_of_occurrences_gen : ('a -> Sexp.t) -> 'a occurrences_gen -> Sexp.t

type occurrences_expr = Locus.occurrences_expr

val occurrences_expr_of_sexp : Sexp.t -> occurrences_expr
val sexp_of_occurrences_expr : occurrences_expr -> Sexp.t

type 'a with_occurrences = 'a Locus.with_occurrences

val with_occurrences_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_occurrences
val sexp_of_with_occurrences : ('a -> Sexp.t) -> 'a with_occurrences -> Sexp.t

type occurrences = Locus.occurrences
val occurrences_of_sexp : Sexp.t -> occurrences
val sexp_of_occurrences : occurrences -> Sexp.t

type hyp_location_flag = Locus.hyp_location_flag

val hyp_location_flag_of_sexp : Sexp.t -> hyp_location_flag
val sexp_of_hyp_location_flag : hyp_location_flag -> Sexp.t

type 'a hyp_location_expr = 'a Locus.hyp_location_expr
val hyp_location_expr_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a hyp_location_expr
val sexp_of_hyp_location_expr : ('a -> Sexp.t) -> 'a hyp_location_expr -> Sexp.t

type 'id clause_expr = 'id Locus.clause_expr

val clause_expr_of_sexp : (Sexp.t -> 'id) -> Sexp.t -> 'id clause_expr
val sexp_of_clause_expr : ('id -> Sexp.t) -> 'id clause_expr -> Sexp.t

type clause = Locus.clause

val clause_of_sexp : Sexp.t -> clause
val sexp_of_clause : clause -> Sexp.t

type clause_atom = Locus.clause_atom

val clause_atom_of_sexp : Sexp.t -> clause_atom
val sexp_of_clause_atom : clause_atom -> Sexp.t

type 'id concrete_clause = 'id Locus.clause_expr

val concrete_clause_of_sexp : (Sexp.t -> 'id) -> Sexp.t -> 'id concrete_clause
val sexp_of_concrete_clause : ('id -> Sexp.t) -> 'id concrete_clause -> Sexp.t

type hyp_location = Locus.clause_atom

val hyp_location_of_sexp : Sexp.t -> hyp_location
val sexp_of_hyp_location : hyp_location -> Sexp.t

type 'id goal_location = 'id Locus.clause_expr

val goal_location_of_sexp : (Sexp.t -> 'id) -> Sexp.t -> 'id goal_location
val sexp_of_goal_location : ('id -> Sexp.t) -> 'id goal_location -> Sexp.t

type simple_clause = Locus.clause_atom
val simple_clause_of_sexp : Sexp.t -> simple_clause
val sexp_of_simple_clause : simple_clause -> Sexp.t

type 'id or_like_first = 'id Locus.clause_expr

val or_like_first_of_sexp : (Sexp.t -> 'id) -> Sexp.t -> 'id or_like_first
val sexp_of_or_like_first : ('id -> Sexp.t) -> 'id or_like_first -> Sexp.t
