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

open Sexplib

type locality = Decl_kinds.locality

val locality_of_sexp : Sexp.t -> locality
val sexp_of_locality : locality -> Sexp.t

type binding_kind = Decl_kinds.binding_kind

val binding_kind_of_sexp : Sexp.t -> binding_kind
val sexp_of_binding_kind : binding_kind -> Sexp.t

type polymorphic = Decl_kinds.polymorphic

val polymorphic_of_sexp : Sexp.t -> polymorphic
val sexp_of_polymorphic : polymorphic -> Sexp.t

type private_flag = Decl_kinds.private_flag

val private_flag_of_sexp : Sexp.t -> private_flag
val sexp_of_private_flag : private_flag -> Sexp.t

type cumulative_inductive_flag = Decl_kinds.cumulative_inductive_flag

val cumulative_inductive_flag_of_sexp : Sexp.t -> cumulative_inductive_flag
val sexp_of_cumulative_inductive_flag : cumulative_inductive_flag -> Sexp.t

type theorem_kind = Decl_kinds.theorem_kind

val theorem_kind_of_sexp : Sexp.t -> theorem_kind
val sexp_of_theorem_kind : theorem_kind -> Sexp.t

type definition_object_kind = Decl_kinds.definition_object_kind

val definition_object_kind_of_sexp : Sexp.t -> definition_object_kind
val sexp_of_definition_object_kind : definition_object_kind -> Sexp.t

type assumption_object_kind = Decl_kinds.assumption_object_kind

val assumption_object_kind_of_sexp : Sexp.t -> assumption_object_kind
val sexp_of_assumption_object_kind : assumption_object_kind -> Sexp.t

type assumption_kind = Decl_kinds.assumption_kind
val assumption_kind_of_sexp : Sexp.t -> assumption_kind
val sexp_of_assumption_kind : assumption_kind -> Sexp.t

type definition_kind = Decl_kinds.definition_kind

val definition_kind_of_sexp : Sexp.t -> definition_kind
val sexp_of_definition_kind : definition_kind -> Sexp.t

type goal_object_kind = Decl_kinds.goal_object_kind

val goal_object_kind_of_sexp : Sexp.t -> goal_object_kind
val sexp_of_goal_object_kind : goal_object_kind -> Sexp.t

type goal_kind = Decl_kinds.goal_kind

val goal_kind_of_sexp : Sexp.t -> goal_kind
val sexp_of_goal_kind : goal_kind -> Sexp.t

type logical_kind = Decl_kinds.logical_kind

val logical_kind_of_sexp : Sexp.t -> logical_kind
val sexp_of_logical_kind : logical_kind -> Sexp.t

type discharge = Decl_kinds.discharge

val discharge_of_sexp : Sexp.t -> discharge
val sexp_of_discharge : discharge -> Sexp.t

