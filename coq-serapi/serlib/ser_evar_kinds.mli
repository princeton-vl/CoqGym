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

(************************************************************************)
(* Evar_kinds.mli                                                       *)
(************************************************************************)
type matching_var_kind = Evar_kinds.matching_var_kind

val matching_var_kind_of_sexp : Sexp.t -> matching_var_kind
val sexp_of_matching_var_kind : matching_var_kind -> Sexp.t

type obligation_definition_status = Evar_kinds.obligation_definition_status

val obligation_definition_status_of_sexp : Sexp.t -> obligation_definition_status
val sexp_of_obligation_definition_status : obligation_definition_status -> Sexp.t

type t = Evar_kinds.t

val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t

