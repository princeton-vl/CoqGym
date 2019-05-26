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

type conv_pb = Evd.conv_pb
val conv_pb_of_sexp : Sexp.t -> conv_pb
val sexp_of_conv_pb : conv_pb -> Sexp.t

type evar_constraint = Evd.evar_constraint

val evar_constraint_of_sexp : Sexp.t -> evar_constraint
val sexp_of_evar_constraint : evar_constraint -> Sexp.t

type unsolvability_explanation = Evd.unsolvability_explanation

val unsolvability_explanation_of_sexp : Sexp.t -> unsolvability_explanation
val sexp_of_unsolvability_explanation : unsolvability_explanation -> Sexp.t
