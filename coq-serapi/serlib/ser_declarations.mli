(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type template_arity = Declarations.template_arity
val template_arity_of_sexp : Sexp.t -> template_arity
val sexp_of_template_arity : template_arity -> Sexp.t

type ('a, 'b) declaration_arity = ('a, 'b) Declarations.declaration_arity

val declaration_arity_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) ->
  Sexp.t -> ('a, 'b) declaration_arity

val sexp_of_declaration_arity :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) ->
  ('a, 'b) declaration_arity -> Sexp.t

type recarg = Declarations.recarg
val recarg_of_sexp : Sexp.t -> recarg
val sexp_of_recarg : recarg -> Sexp.t

type wf_paths = recarg Rtree.t
val wf_paths_of_sexp : Sexp.t -> wf_paths
val sexp_of_wf_paths : wf_paths -> Sexp.t

type regular_inductive_arity = Declarations.regular_inductive_arity
val regular_inductive_arity_of_sexp : Sexp.t -> regular_inductive_arity
val sexp_of_regular_inductive_arity : regular_inductive_arity -> Sexp.t

type inductive_arity = Declarations.inductive_arity
val inductive_arity_of_sexp : Sexp.t -> inductive_arity
val sexp_of_inductive_arity : inductive_arity -> Sexp.t

type one_inductive_body = Declarations.one_inductive_body
val one_inductive_body_of_sexp : Sexp.t -> one_inductive_body
val sexp_of_one_inductive_body : one_inductive_body -> Sexp.t

type set_predicativity = Declarations.set_predicativity
val set_predicativity_of_sexp : Sexp.t -> set_predicativity
val sexp_of_set_predicativity : set_predicativity -> Sexp.t

type engagement = Declarations.engagement
val engagement_of_sexp : Sexp.t -> engagement
val sexp_of_engagement : engagement -> Sexp.t

type typing_flags = Declarations.typing_flags
val typing_flags_of_sexp : Sexp.t -> typing_flags
val sexp_of_typing_flags : typing_flags -> Sexp.t

type constant_body = Declarations.constant_body
val sexp_of_constant_body : constant_body -> Sexp.t

(* type record_body = Declarations.record_body
 * val record_body_of_sexp : Sexp.t -> record_body
 * val sexp_of_record_body : record_body -> Sexp.t *)

type recursivity_kind = Declarations.recursivity_kind
val recursivity_kind_of_sexp : Sexp.t -> recursivity_kind
val sexp_of_recursivity_kind : recursivity_kind -> Sexp.t

type mutual_inductive_body = Declarations.mutual_inductive_body
val mutual_inductive_body_of_sexp : Sexp.t -> mutual_inductive_body
val sexp_of_mutual_inductive_body : mutual_inductive_body -> Sexp.t

type module_body = Declarations.module_body
val sexp_of_module_body : module_body -> Sexp.t

type module_type_body = Declarations.module_type_body
val sexp_of_module_type_body : module_type_body -> Sexp.t