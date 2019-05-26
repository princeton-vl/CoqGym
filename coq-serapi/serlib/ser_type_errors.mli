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

type arity_error = Type_errors.arity_error
val arity_error_of_sexp : Sexp.t -> arity_error
val sexp_of_arity_error : arity_error -> Sexp.t

type guard_error = Type_errors.guard_error
val guard_error_of_sexp : Sexp.t -> guard_error
val sexp_of_guard_error : guard_error -> Sexp.t

type ('c, 't) ptype_error  = ('c, 't) Type_errors.ptype_error
val ptype_error_of_sexp :
  (Sexp.t -> 'constr) -> (Sexp.t -> 'types) ->
  Sexp.t -> ('constr, 'types) ptype_error

val sexp_of_ptype_error :
  ('constr -> Sexp.t) ->
  ('types -> Sexp.t) ->
  ('constr, 'types) ptype_error -> Sexp.t

type type_error  = Type_errors.type_error
val type_error_of_sexp : Sexp.t -> type_error
val sexp_of_type_error : type_error -> Sexp.t

