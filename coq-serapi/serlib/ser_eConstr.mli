(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type t = EConstr.t

val sexp_of_t : t -> Sexp.t
val t_of_sexp : Sexp.t -> t

type existential = EConstr.existential

val existential_of_sexp : Sexp.t -> existential
val sexp_of_existential : existential -> Sexp.t

type constr = t

val sexp_of_constr : constr -> Sexp.t
val constr_of_sexp : Sexp.t -> constr

type types = t

val sexp_of_types : types -> Sexp.t
val types_of_sexp : Sexp.t -> types

type unsafe_judgment = EConstr.unsafe_judgment

val sexp_of_unsafe_judgment : unsafe_judgment -> Sexp.t
val unsafe_judgment_of_sexp : Sexp.t -> unsafe_judgment
