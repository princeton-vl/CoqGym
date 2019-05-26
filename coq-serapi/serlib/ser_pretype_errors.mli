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

type unification_error = Pretype_errors.unification_error
val unification_error_of_sexp : Sexp.t -> unification_error
val sexp_of_unification_error : unification_error -> Sexp.t

type position = Pretype_errors.position
val position_of_sexp : Sexp.t -> position
val sexp_of_position : position -> Sexp.t

type position_reporting = Pretype_errors.position_reporting
val position_reporting_of_sexp : Sexp.t -> position_reporting
val sexp_of_position_reporting : position_reporting -> Sexp.t

type subterm_unification_error = Pretype_errors.subterm_unification_error
val subterm_unification_error_of_sexp : Sexp.t -> subterm_unification_error
val sexp_of_subterm_unification_error : subterm_unification_error -> Sexp.t

type pretype_error = Pretype_errors.pretype_error
val pretype_error_of_sexp : Sexp.t -> pretype_error
val sexp_of_pretype_error : pretype_error -> Sexp.t
