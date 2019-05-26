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

type env = Environ.env

val env_of_sexp : Sexp.t -> env
val sexp_of_env : env -> Sexp.t

type ('constr, 'types) punsafe_judgment = ('constr, 'types) Environ.punsafe_judgment

val punsafe_judgment_of_sexp :
  (Sexp.t -> 'constr) ->
  (Sexp.t -> 'types) -> Sexp.t ->
  ('constr, 'types) punsafe_judgment
val sexp_of_punsafe_judgment :
  ('constr -> Sexplib.Sexp.t) ->
  ('types -> Sexplib.Sexp.t) ->
  ('constr, 'types) punsafe_judgment -> Sexp.t

type unsafe_judgment = Environ.unsafe_judgment
val unsafe_judgment_of_sexp : Sexp.t -> unsafe_judgment
val sexp_of_unsafe_judgment : unsafe_judgment -> Sexp.t
