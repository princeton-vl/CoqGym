(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type class_rawexpr = Vernacexpr.class_rawexpr
val class_rawexpr_of_sexp : Sexp.t -> class_rawexpr
val sexp_of_class_rawexpr : class_rawexpr -> Sexp.t

type goal_identifier = Vernacexpr.goal_identifier
val goal_identifier_of_sexp : Sexp.t -> goal_identifier
val sexp_of_goal_identifier : goal_identifier -> Sexp.t

type scope_name = Vernacexpr.scope_name
val scope_name_of_sexp : Sexp.t -> scope_name
val sexp_of_scope_name : scope_name -> Sexp.t

type goal_reference = Vernacexpr.goal_reference
val goal_reference_of_sexp : Sexp.t -> goal_reference
val sexp_of_goal_reference : goal_reference -> Sexp.t

type printable = Vernacexpr.printable
val printable_of_sexp : Sexp.t -> printable
val sexp_of_printable : printable -> Sexp.t

type search_about_item = Vernacexpr.search_about_item
val search_about_item_of_sexp : Sexp.t -> search_about_item
val sexp_of_search_about_item : search_about_item -> Sexp.t

type searchable = Vernacexpr.searchable
val searchable_of_sexp : Sexp.t -> searchable
val sexp_of_searchable : searchable -> Sexp.t

type locatable = Vernacexpr.locatable
val locatable_of_sexp : Sexp.t -> locatable
val sexp_of_locatable : locatable -> Sexp.t

type showable = Vernacexpr.showable
val showable_of_sexp : Sexp.t -> showable
val sexp_of_showable : showable -> Sexp.t

type comment = Vernacexpr.comment
val comment_of_sexp : Sexp.t -> comment
val sexp_of_comment : comment -> Sexp.t

type search_restriction = Vernacexpr.search_restriction
val search_restriction_of_sexp : Sexp.t -> search_restriction
val sexp_of_search_restriction : search_restriction -> Sexp.t

type rec_flag = Vernacexpr.rec_flag
val rec_flag_of_sexp : Sexp.t -> rec_flag
val sexp_of_rec_flag : rec_flag -> Sexp.t

type verbose_flag = Vernacexpr.verbose_flag
val verbose_flag_of_sexp : Sexp.t -> verbose_flag
val sexp_of_verbose_flag : verbose_flag -> Sexp.t

type coercion_flag = Vernacexpr.coercion_flag
val coercion_flag_of_sexp : Sexp.t -> coercion_flag
val sexp_of_coercion_flag : coercion_flag -> Sexp.t

type inductive_flag = Vernacexpr.inductive_flag
val inductive_flag_of_sexp : Sexp.t -> inductive_flag
val sexp_of_inductive_flag : inductive_flag -> Sexp.t

type instance_flag = Vernacexpr.instance_flag
val instance_flag_of_sexp : Sexp.t -> instance_flag
val sexp_of_instance_flag : instance_flag -> Sexp.t

type export_flag = Vernacexpr.export_flag
val export_flag_of_sexp : Sexp.t -> export_flag
val sexp_of_export_flag : export_flag -> Sexp.t

type onlyparsing_flag = Vernacexpr.onlyparsing_flag
val onlyparsing_flag_of_sexp : Sexp.t -> onlyparsing_flag
val sexp_of_onlyparsing_flag : onlyparsing_flag -> Sexp.t

type locality_flag = Vernacexpr.locality_flag
val locality_flag_of_sexp : Sexp.t -> locality_flag
val sexp_of_locality_flag : locality_flag -> Sexp.t

(* type obsolete_locality = Vernacexpr.obsolete_locality
 * val obsolete_locality_of_sexp : Sexp.t -> obsolete_locality
 * val sexp_of_obsolete_locality : obsolete_locality -> Sexp.t *)

type option_value = Vernacexpr.option_value
val option_value_of_sexp : Sexp.t -> option_value
val sexp_of_option_value : option_value -> Sexp.t

type option_ref_value = Vernacexpr.option_ref_value
val option_ref_value_of_sexp : Sexp.t -> option_ref_value
val sexp_of_option_ref_value : option_ref_value -> Sexp.t

(* type plident = Vernacexpr.plident
 * val plident_of_sexp : Sexp.t -> plident
 * val sexp_of_plident : plident -> Sexp.t *)

type sort_expr = Vernacexpr.sort_expr
val sort_expr_of_sexp : Sexp.t -> sort_expr
val sexp_of_sort_expr : sort_expr -> Sexp.t

type definition_expr = Vernacexpr.definition_expr
val definition_expr_of_sexp : Sexp.t -> definition_expr
val sexp_of_definition_expr : definition_expr -> Sexp.t

type fixpoint_expr = Vernacexpr.fixpoint_expr
val fixpoint_expr_of_sexp : Sexp.t -> fixpoint_expr
val sexp_of_fixpoint_expr : fixpoint_expr -> Sexp.t

type cofixpoint_expr = Vernacexpr.cofixpoint_expr
val cofixpoint_expr_of_sexp : Sexp.t -> cofixpoint_expr
val sexp_of_cofixpoint_expr : cofixpoint_expr -> Sexp.t

type local_decl_expr = Vernacexpr.local_decl_expr
val local_decl_expr_of_sexp : Sexp.t -> local_decl_expr
val sexp_of_local_decl_expr : local_decl_expr -> Sexp.t

type inductive_kind = Vernacexpr.inductive_kind
val inductive_kind_of_sexp : Sexp.t -> inductive_kind
val sexp_of_inductive_kind : inductive_kind -> Sexp.t

type decl_notation = Vernacexpr.decl_notation
val decl_notation_of_sexp : Sexp.t -> decl_notation
val sexp_of_decl_notation : decl_notation -> Sexp.t

type simple_binder = Vernacexpr.simple_binder
val simple_binder_of_sexp : Sexp.t -> simple_binder
val sexp_of_simple_binder : simple_binder -> Sexp.t

type class_binder = Vernacexpr.class_binder

val class_binder_of_sexp : Sexp.t -> class_binder
val sexp_of_class_binder : class_binder -> Sexp.t

type 'a with_coercion = 'a Vernacexpr.with_coercion

val with_coercion_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_coercion
val sexp_of_with_coercion : ('a -> Sexp.t) -> 'a with_coercion -> Sexp.t

type 'a with_instance = 'a Vernacexpr.with_instance
val with_instance_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_instance
val sexp_of_with_instance : ('a -> Sexp.t) -> 'a with_instance -> Sexp.t

type 'a with_notation = 'a Vernacexpr.with_notation
val with_notation_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_notation
val sexp_of_with_notation : ('a -> Sexp.t) -> 'a with_notation -> Sexp.t

type 'a with_priority = 'a Vernacexpr.with_priority
val with_priority_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_priority
val sexp_of_with_priority : ('a -> Sexp.t) -> 'a with_priority -> Sexp.t

type constructor_expr = Vernacexpr.constructor_expr
val constructor_expr_of_sexp : Sexp.t -> constructor_expr
val sexp_of_constructor_expr : constructor_expr -> Sexp.t

type constructor_list_or_record_decl_expr = Vernacexpr.constructor_list_or_record_decl_expr

val constructor_list_or_record_decl_expr_of_sexp :
  Sexp.t -> constructor_list_or_record_decl_expr
val sexp_of_constructor_list_or_record_decl_expr :
  constructor_list_or_record_decl_expr -> Sexp.t

type inductive_expr = Vernacexpr.inductive_expr

val inductive_expr_of_sexp : Sexp.t -> inductive_expr
val sexp_of_inductive_expr : inductive_expr -> Sexp.t

type one_inductive_expr = Vernacexpr.one_inductive_expr

val one_inductive_expr_of_sexp : Sexp.t -> one_inductive_expr
val sexp_of_one_inductive_expr : one_inductive_expr -> Sexp.t

type proof_expr = Vernacexpr.proof_expr

val proof_expr_of_sexp : Sexp.t -> proof_expr
val sexp_of_proof_expr : proof_expr -> Sexp.t

(* type grammar_tactic_prod_item_expr = Vernacexpr.grammar_tactic_prod_item_expr *)
(* val grammar_tactic_prod_item_expr_of_sexp : Sexp.t -> grammar_tactic_prod_item_expr *)
(* val sexp_of_grammar_tactic_prod_item_expr : grammar_tactic_prod_item_expr -> Sexp.t *)

(* type syntax_modifier = Vernacexpr.syntax_modifier *)

(* val syntax_modifier_of_sexp : Sexp.t -> syntax_modifier *)
(* val sexp_of_syntax_modifier : syntax_modifier -> Sexp.t *)

type proof_end = Vernacexpr.proof_end
val proof_end_of_sexp : Sexp.t -> proof_end
val sexp_of_proof_end : proof_end -> Sexp.t

type scheme = Vernacexpr.scheme
val scheme_of_sexp : Sexp.t -> scheme
val sexp_of_scheme : scheme -> Sexp.t

type section_subset_expr = Vernacexpr.section_subset_expr
val section_subset_expr_of_sexp : Sexp.t -> section_subset_expr
val sexp_of_section_subset_expr : section_subset_expr -> Sexp.t

type extend_name = Vernacexpr.extend_name
val extend_name_of_sexp : Sexp.t -> extend_name
val sexp_of_extend_name : extend_name -> Sexp.t

type register_kind = Vernacexpr.register_kind
val register_kind_of_sexp : Sexp.t -> register_kind
val sexp_of_register_kind : register_kind -> Sexp.t

type module_ast_inl = Vernacexpr.module_ast_inl

val module_ast_inl_of_sexp : Sexp.t -> module_ast_inl
val sexp_of_module_ast_inl : module_ast_inl -> Sexp.t

type module_binder = Vernacexpr.module_binder

val module_binder_of_sexp : Sexp.t -> module_binder
val sexp_of_module_binder : module_binder -> Sexp.t

type vernac_expr = Vernacexpr.vernac_expr
(* and  vernac_list = Vernacexpr.vernac_list *)
(* and  located_vernac_expr = Vernacexpr.located_vernac_expr *)

val vernac_expr_of_sexp : Sexp.t -> vernac_expr
val sexp_of_vernac_expr : vernac_expr -> Sexp.t

(* val located_vernac_expr_of_sexp : Sexp.t -> located_vernac_expr *)
(* val sexp_of_located_vernac_expr : located_vernac_expr -> Sexp.t *)

(* val vernac_list_of_sexp : Sexp.t -> vernac_list *)
(* val sexp_of_vernac_list : vernac_list -> Sexp.t *)

type vernac_control = Vernacexpr.vernac_control
val vernac_control_of_sexp : Sexp.t -> vernac_control
val sexp_of_vernac_control : vernac_control -> Sexp.t
