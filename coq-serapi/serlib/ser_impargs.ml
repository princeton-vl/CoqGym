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
open Sexplib.Std

module Names = Ser_names

type argument_position =
  [%import: Impargs.argument_position]
  [@@deriving sexp]

type implicit_explanation =
  [%import: Impargs.implicit_explanation]
  [@@deriving sexp]

type maximal_insertion =
  [%import: Impargs.maximal_insertion]
  [@@deriving sexp]

type force_inference =
  [%import: Impargs.force_inference]
  [@@deriving sexp]

(* XXX: Careful here, we break abstraction, so this must be kept in sync with Coq. *)
type _implicit_side_condition = DefaultImpArgs | LessArgsThan of int
  [@@deriving sexp]

type implicit_side_condition = Impargs.implicit_side_condition

let implicit_side_condition_of_sexp (sexp : Sexp.t) : implicit_side_condition =
  Obj.magic (_implicit_side_condition_of_sexp sexp)

let sexp_of_implicit_side_condition (isc : implicit_side_condition) : Sexp.t =
  sexp_of__implicit_side_condition Obj.(magic isc)

type implicit_status =
  [%import: Impargs.implicit_status]
  [@@deriving sexp]

type implicits_list =
  [%import: Impargs.implicits_list]
  [@@deriving sexp]




