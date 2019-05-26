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

module Loc         = Ser_loc
module CAst        = Ser_cAst
module Names       = Ser_names
module Flags       = Ser_flags
module Sorts       = Ser_sorts
module Univ        = Ser_univ
module UnivNames   = Ser_univNames
module Conv_oracle = Ser_conv_oracle
module Declarations= Ser_declarations
module Decl_kinds  = Ser_decl_kinds
module Genarg      = Ser_genarg
module Declaremods = Ser_declaremods
module Libnames    = Ser_libnames
module Extend      = Ser_extend
module Stateid     = Ser_stateid
module Glob_term     = Ser_glob_term
module Goal_select   = Ser_goal_select
module Proof_global  = Ser_proof_global
module Proof_bullet  = Ser_proof_bullet
module Constrexpr    = Ser_constrexpr
module Notation_term = Ser_notation_term
module Hints         = Ser_hints
module Goptions      = Ser_goptions
module Genredexpr    = Ser_genredexpr
module Universes     = Ser_universes

type class_rawexpr = [%import: Vernacexpr.class_rawexpr]
  [@@deriving sexp]

type goal_identifier = [%import: Vernacexpr.goal_identifier]
  [@@deriving sexp]

type scope_name      = [%import: Vernacexpr.scope_name]
  [@@deriving sexp]

type goal_reference = [%import: Vernacexpr.goal_reference]
  [@@deriving sexp]

type printable = [%import: Vernacexpr.printable]
  [@@deriving sexp]

type vernac_cumulative =
  [%import: Vernacexpr.vernac_cumulative]
  [@@deriving sexp]

type search_about_item =
  [%import: Vernacexpr.search_about_item]
  [@@deriving sexp]

type searchable =
  [%import: Vernacexpr.searchable]
  [@@deriving sexp]

type locatable = [%import: Vernacexpr.locatable]
  [@@deriving sexp]

type showable =  [%import: Vernacexpr.showable]
  [@@deriving sexp]

type comment =
  [%import: Vernacexpr.comment]
  [@@deriving sexp]

type search_restriction =  [%import: Vernacexpr.search_restriction]
  [@@deriving sexp]

type rec_flag          = [%import: Vernacexpr.rec_flag          ] [@@deriving sexp]
type verbose_flag      = [%import: Vernacexpr.verbose_flag      ] [@@deriving sexp]
type coercion_flag     = [%import: Vernacexpr.coercion_flag     ] [@@deriving sexp]
type inductive_flag    = [%import: Vernacexpr.inductive_flag    ] [@@deriving sexp]
type instance_flag     = [%import: Vernacexpr.instance_flag     ] [@@deriving sexp]
type export_flag       = [%import: Vernacexpr.export_flag       ] [@@deriving sexp]
type onlyparsing_flag  = [%import: Vernacexpr.onlyparsing_flag  ] [@@deriving sexp]
type locality_flag     = [%import: Vernacexpr.locality_flag     ] [@@deriving sexp]
(* type obsolete_locality = [%import: Vernacexpr.obsolete_locality ] [@@deriving sexp] *)

type option_value = Goptions.option_value
  [@@deriving sexp]
  (* [%import: Vernacexpr.option_value] *)

type option_ref_value =
  [%import: Vernacexpr.option_ref_value]
  [@@deriving sexp]

(* type plident =
 *   [%import: Vernacexpr.plident ]
 *   [@@deriving sexp] *)

type sort_expr =
  [%import: Vernacexpr.sort_expr]
  [@@deriving sexp]

type definition_expr =
  [%import: Vernacexpr.definition_expr]
  [@@deriving sexp]

type fixpoint_expr =
  [%import: Vernacexpr.fixpoint_expr]
  [@@deriving sexp]

type cofixpoint_expr =
  [%import: Vernacexpr.cofixpoint_expr]
  [@@deriving sexp]

type local_decl_expr =
  [%import: Vernacexpr.local_decl_expr]
  [@@deriving sexp]

type inductive_kind =
  [%import: Vernacexpr.inductive_kind]
  [@@deriving sexp]

type decl_notation =
  [%import: Vernacexpr.decl_notation]
  [@@deriving sexp]

type simple_binder =
  [%import: Vernacexpr.simple_binder]
  [@@deriving sexp]

type class_binder =
  [%import: Vernacexpr.class_binder]
  [@@deriving sexp]

type 'a with_coercion =
  [%import: 'a Vernacexpr.with_coercion]
  [@@deriving sexp]

type 'a with_instance =
  [%import: 'a Vernacexpr.with_instance]
  [@@deriving sexp]

type 'a with_notation =
  [%import: 'a Vernacexpr.with_notation]
  [@@deriving sexp]

type 'a with_priority =
  [%import: 'a Vernacexpr.with_priority]
  [@@deriving sexp]

type constructor_expr =
  [%import: Vernacexpr.constructor_expr]
  [@@deriving sexp]

type constructor_list_or_record_decl_expr =
  [%import: Vernacexpr.constructor_list_or_record_decl_expr]
  [@@deriving sexp]

type inductive_expr =
  [%import: Vernacexpr.inductive_expr]
  [@@deriving sexp]

type one_inductive_expr =
  [%import: Vernacexpr.one_inductive_expr]
  [@@deriving sexp]

type proof_expr =
  [%import: Vernacexpr.proof_expr]
  [@@deriving sexp]

type syntax_modifier =
  [%import: Vernacexpr.syntax_modifier]
  [@@deriving sexp]

type proof_end =
  [%import: Vernacexpr.proof_end]
  [@@deriving sexp]

type scheme =
  [%import: Vernacexpr.scheme]
  [@@deriving sexp]

type section_subset_expr =
  [%import: Vernacexpr.section_subset_expr]
  [@@deriving sexp]

type extend_name =
  [%import: Vernacexpr.extend_name]
  [@@deriving sexp]

type register_kind =
  [%import: Vernacexpr.register_kind]
  [@@deriving sexp]

type module_ast_inl =
  [%import: Vernacexpr.module_ast_inl]
  [@@deriving sexp]

type module_binder =
  [%import: Vernacexpr.module_binder]
  [@@deriving sexp]

type typeclass_constraint =
  [%import: Vernacexpr.typeclass_constraint]
  [@@deriving sexp]

type vernac_flag_value =
  [%import: Vernacexpr.vernac_flag_value]
and vernac_flags =
  [%import: Vernacexpr.vernac_flags]
  [@@deriving sexp]

type vernac_expr           = [%import: Vernacexpr.vernac_expr]
and vernac_implicit_status = [%import: Vernacexpr.vernac_implicit_status]
and vernac_argument_status = [%import: Vernacexpr.vernac_argument_status]
  [@@deriving sexp]

type vernac_control =
  [%import: Vernacexpr.vernac_control]
  [@@deriving sexp]
