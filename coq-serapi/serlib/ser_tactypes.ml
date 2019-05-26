(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
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

module CAst        = Ser_cAst
module Names       = Ser_names
module Namegen     = Ser_namegen

type 'a intro_pattern_action_expr =
  [%import: 'a Tactypes.intro_pattern_action_expr]
and 'a intro_pattern_expr =
  [%import: 'a Tactypes.intro_pattern_expr]
and 'a or_and_intro_pattern_expr =
  [%import: 'a Tactypes.or_and_intro_pattern_expr]
  [@@deriving sexp]

type quantified_hypothesis =
  [%import: Tactypes.quantified_hypothesis]
  [@@deriving sexp]

type 'a explicit_bindings =
  [%import: 'a Tactypes.explicit_bindings]
  [@@deriving sexp]

type 'a bindings =
  [%import: 'a Tactypes.bindings]
  [@@deriving sexp]

type 'a with_bindings =
  [%import: 'a Tactypes.with_bindings]
  [@@deriving sexp]

type 'a delayed_open =
  [%import: 'a Tactypes.delayed_open]

let sexp_of_delayed_open _ = Serlib_base.sexp_of_opaque ~typ:"wit_bindings/top"
let delayed_open_of_sexp _ = Serlib_base.opaque_of_sexp ~typ:"wit_bindings/top";
