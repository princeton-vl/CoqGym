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

type glob_level = Glob_term.glob_level
val glob_level_of_sexp : Sexp.t -> Glob_term.glob_level
val sexp_of_glob_level : Glob_term.glob_level -> Sexp.t

type glob_sort = Glob_term.glob_sort
val glob_sort_of_sexp : Sexp.t -> Glob_term.glob_sort
val sexp_of_glob_sort : Glob_term.glob_sort -> Sexp.t

type 'a cast_type = 'a Glob_term.cast_type
val cast_type_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a Glob_term.cast_type
val sexp_of_cast_type : ('a -> Sexp.t) -> 'a Glob_term.cast_type -> Sexp.t

type glob_constraint = Glob_term.glob_constraint
val glob_constraint_of_sexp : Sexp.t -> Glob_term.glob_constraint
val sexp_of_glob_constraint : Glob_term.glob_constraint -> Sexp.t

type existential_name = Glob_term.existential_name

type cases_pattern    = Glob_term.cases_pattern

type glob_constr        = Glob_term.glob_constr
and glob_decl           = Glob_term.glob_decl
and fix_recursion_order = Glob_term.fix_recursion_order
and fix_kind            = Glob_term.fix_kind
and predicate_pattern   = Glob_term.predicate_pattern
and tomatch_tuple       = Glob_term.tomatch_tuple
and tomatch_tuples      = Glob_term.tomatch_tuples
and cases_clause        = Glob_term.cases_clause
and cases_clauses       = Glob_term.cases_clauses

val existential_name_of_sexp : Sexp.t -> Glob_term.existential_name
val sexp_of_existential_name : Glob_term.existential_name -> Sexp.t

val cases_pattern_of_sexp : Sexp.t -> cases_pattern
val sexp_of_cases_pattern : cases_pattern -> Sexp.t

val glob_constr_of_sexp : Sexp.t -> glob_constr
val sexp_of_glob_constr : glob_constr -> Sexp.t

val glob_decl_of_sexp : Sexp.t -> glob_decl
val sexp_of_glob_decl : glob_decl -> Sexp.t

val fix_recursion_order_of_sexp : Sexp.t -> fix_recursion_order
val sexp_of_fix_recursion_order : fix_recursion_order -> Sexp.t

val fix_kind_of_sexp : Sexp.t -> fix_kind
val sexp_of_fix_kind : fix_kind -> Sexp.t

val predicate_pattern_of_sexp : Sexp.t -> predicate_pattern
val sexp_of_predicate_pattern : predicate_pattern -> Sexp.t

val tomatch_tuple_of_sexp : Sexp.t -> tomatch_tuple
val sexp_of_tomatch_tuple : tomatch_tuple -> Sexp.t

val tomatch_tuples_of_sexp : Sexp.t -> tomatch_tuples
val sexp_of_tomatch_tuples : tomatch_tuples -> Sexp.t

val cases_clause_of_sexp : Sexp.t -> cases_clause
val sexp_of_cases_clause : cases_clause -> Sexp.t

val cases_clauses_of_sexp : Sexp.t -> cases_clauses
val sexp_of_cases_clauses : cases_clauses -> Sexp.t
