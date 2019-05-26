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
open Sexplib.Conv
open Declarations

module Names   = Ser_names
module Context = Ser_context
module Constr  = Ser_constr
module Sorts   = Ser_sorts
module Univ    = Ser_univ
module Decl_kinds = Ser_decl_kinds
module Vmvalues = Ser_vmvalues
module Conv_oracle = Ser_conv_oracle
module Mod_subst = Ser_mod_subst
module Opaqueproof = Ser_opaqueproof
module Cemitcodes = Ser_cemitcodes
module Retroknowledge = Ser_retroknowledge

type template_arity =
  [%import: Declarations.template_arity]
  [@@deriving sexp]

type ('a, 'b) declaration_arity =
  [%import: ('a, 'b) Declarations.declaration_arity]
  [@@deriving sexp]

type recarg =
  [%import: Declarations.recarg]
  [@@deriving sexp]

(* XXX: Fixme *)
module Rtree = struct

  type 'a t = 'a Rtree.t

  let t_of_sexp f s = Rtree.mk_node (f s) [||]

  let sexp_of_t f t =
    let n, ll = Rtree.dest_node t in
    Sexp.(List [Atom "RTree"; f n; sexp_of_int @@ Array.length ll])

end

type wf_paths =
  [%import: Declarations.wf_paths]
  [@@deriving sexp]

type regular_inductive_arity =
  [%import: Declarations.regular_inductive_arity
  [@with Term.sorts := Sorts.t;]]
  [@@deriving sexp]

type inductive_arity =
  [%import: Declarations.inductive_arity]
  [@@deriving sexp]

type one_inductive_body =
  [%import: Declarations.one_inductive_body]
  [@@deriving sexp]

type set_predicativity =
  [%import: Declarations.set_predicativity]
  [@@deriving sexp]

type engagement =
  [%import: Declarations.engagement]
  [@@deriving sexp]

type inline = 
  [%import: Declarations.inline]
  [@@deriving sexp]

type constant_def = 
  [%import: Declarations.constant_def]
  [@@deriving sexp_of]

type constant_universes = 
  [%import: Declarations.constant_universes]
  [@@deriving sexp]

type typing_flags =
  [%import: Declarations.typing_flags]
  [@@deriving sexp]

type constant_body = 
  [%import: Declarations.constant_body]
  [@@deriving sexp_of]

(* type record_body =
 *   [%import: Declarations.record_body
 *   [@with Context.section_context := Context.Named.t;]]
 *   [@@deriving sexp] *)

let sexp_of_module_retroknowledge _ = Serlib_base.sexp_of_opaque ~typ:"Declarations.module_retroknowledge" 
 
type abstract_inductive_universes =
  [%import: Declarations.abstract_inductive_universes]
  [@@deriving sexp]

type recursivity_kind =
  [%import: Declarations.recursivity_kind]
  [@@deriving sexp]

type record_info =
  [%import: Declarations.record_info]
  [@@deriving sexp]

type mutual_inductive_body =
  [%import: Declarations.mutual_inductive_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp]

type ('ty,'a) functorize =
  [%import: ('ty, 'a) Declarations.functorize]
  [@@deriving sexp_of]

type with_declaration =
  [%import: Declarations.with_declaration]
  [@@deriving sexp_of]

type module_alg_expr =
  [%import: Declarations.module_alg_expr]
  [@@deriving sexp_of]

type structure_field_body =
  [%import: Declarations.structure_field_body]
  [@@deriving sexp_of]

and structure_body =
  [%import: Declarations.structure_body]
  [@@deriving sexp_of]

and module_signature =
  [%import: Declarations.module_signature]
  [@@deriving sexp_of]

and module_expression = 
  [%import: Declarations.module_expression]
  [@@deriving sexp_of]

and module_implementation =
  [%import: Declarations.module_implementation]
  [@@deriving sexp_of]

and 'a generic_module_body = 
  [%import: 'a Declarations.generic_module_body]
  [@@deriving sexp_of]

and module_body = 
  [%import: Declarations.module_body]
  [@@deriving sexp_of]
  
and module_type_body = 
  [%import: Declarations.module_type_body]
  [@@deriving sexp_of]