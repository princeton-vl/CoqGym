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

(* open Sexplib.Std *)

module Loc        = Ser_loc
module Names      = Ser_names
module Tok        = Ser_tok

(* type notation_spec = *)
(*   [%import: Notation_term.notation_spec] *)
(*   [@@deriving sexp] *)

(* type syntax_modifier = *)
(*   [%import: Notation_term.syntax_modifier] *)
(*   [@@deriving sexp] *)

type constr_as_binder_kind =
  [%import: Notation_term.constr_as_binder_kind]
  [@@deriving sexp]

type notation_var_internalization_type =
  [%import: Notation_term.notation_var_internalization_type]
  [@@deriving sexp]

