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

open Sexplib.Conv
module Names     = Ser_names
module Constr    = Ser_constr
module Glob_term = Ser_glob_term
module EConstr   = Ser_eConstr

type constr_under_binders =
  [%import: Ltac_pretype.constr_under_binders]
  [@@deriving sexp]

type closure = [%import: Ltac_pretype.closure]
and closed_glob_constr = [%import: Ltac_pretype.closed_glob_constr]
  [@@deriving sexp]

