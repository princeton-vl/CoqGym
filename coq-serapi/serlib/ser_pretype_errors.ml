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

open Sexplib.Std

module Names = Ser_names

module Term        = Ser_constr
module Evd         = Ser_evd
module Evar        = Ser_evar
module Environ     = Ser_environ
module EConstr     = Ser_eConstr
module Univ        = Ser_univ
module Type_errors = Ser_type_errors
module Locus       = Ser_locus
module Evar_kinds  = Ser_evar_kinds

type unification_error =
  [%import: Pretype_errors.unification_error]
  [@@deriving sexp]

type position =
  [%import: Pretype_errors.position]
  [@@deriving sexp]

type position_reporting =
  [%import: Pretype_errors.position_reporting]
  [@@deriving sexp]

type subterm_unification_error =
  [%import: Pretype_errors.subterm_unification_error]
  [@@deriving sexp]

type type_error =
  [%import: Pretype_errors.type_error]
  [@@deriving sexp]

type pretype_error =
  [%import: Pretype_errors.pretype_error]
  [@@deriving sexp]
