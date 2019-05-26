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

module Loc   = Ser_loc
module Names = Ser_names

open Ltac_plugin

type 'a grammar_tactic_prod_item_expr =
  [%import: 'a Tacentries.grammar_tactic_prod_item_expr]
  [@@deriving sexp]

type raw_argument =
  [%import: Tacentries.raw_argument]
  [@@deriving sexp]
