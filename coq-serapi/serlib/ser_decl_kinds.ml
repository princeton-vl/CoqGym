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

(**********************************************************************)
(* Decl_kinds                                                         *)
(**********************************************************************)

open Sexplib.Std

type locality = [%import: Decl_kinds.locality]
  [@@deriving sexp]

type binding_kind = [%import: Decl_kinds.binding_kind]
  [@@deriving sexp]

type polymorphic =
  [%import: Decl_kinds.polymorphic]
  [@@deriving sexp]

type private_flag =
  [%import: Decl_kinds.private_flag]
  [@@deriving sexp]

type cumulative_inductive_flag =
  [%import: Decl_kinds.cumulative_inductive_flag]
  [@@deriving sexp]

type theorem_kind =
  [%import: Decl_kinds.theorem_kind]
  [@@deriving sexp]

type definition_object_kind =
  [%import: Decl_kinds.definition_object_kind]
  [@@deriving sexp]

type assumption_object_kind =
  [%import: Decl_kinds.assumption_object_kind]
  [@@deriving sexp]

type assumption_kind =
  [%import: Decl_kinds.assumption_kind]
  [@@deriving sexp]

type definition_kind =
  [%import: Decl_kinds.definition_kind]
  [@@deriving sexp]

type goal_object_kind =
  [%import: Decl_kinds.goal_object_kind]
  [@@deriving sexp]

type goal_kind =
  [%import: Decl_kinds.goal_kind]
  [@@deriving sexp]

type logical_kind =
  [%import: Decl_kinds.logical_kind]
  [@@deriving sexp]

type discharge =
  [%import: Decl_kinds.discharge]
  [@@deriving sexp]
