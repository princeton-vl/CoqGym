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

open Ltac_plugin

module CAst         = Ser_cAst
module Constrexpr   = Ser_constrexpr
module Tactypes     = Ser_tactypes
module Tacexpr      = Ser_tacexpr
module Genintern    = Ser_genintern

(* Tacarg *)
module A1 = struct
  type h1 = Constrexpr.constr_expr Tactypes.intro_pattern_expr CAst.t
  [@@deriving sexp]
  type h2 = Genintern.glob_constr_and_expr Tactypes.intro_pattern_expr CAst.t
  [@@deriving sexp]
  type h3 = Tacexpr.intro_pattern
  [@@deriving sexp]
end

let ser_wit_intropattern = let open A1 in Ser_genarg.
  { raw_ser = sexp_of_h1
  ; raw_des = h1_of_sexp

  ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp

  ; top_ser = sexp_of_h3
  ; top_des = h3_of_sexp
  }

let ser_wit_destruction_arg = Ser_genarg.{
    raw_ser = Ser_tactics.sexp_of_destruction_arg (Ser_tactypes.sexp_of_with_bindings Ser_constrexpr.sexp_of_constr_expr);
    glb_ser = Ser_tactics.sexp_of_destruction_arg (Ser_tactypes.sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr);
    top_ser = Ser_tactics.(sexp_of_destruction_arg Ser_tacexpr.sexp_of_delayed_open_constr_with_bindings);

    raw_des = Ser_tactics.destruction_arg_of_sexp (Ser_tactypes.with_bindings_of_sexp Ser_constrexpr.constr_expr_of_sexp);
    glb_des = Ser_tactics.destruction_arg_of_sexp (Ser_tactypes.with_bindings_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp);
    top_des = Ser_tactics.(destruction_arg_of_sexp Ser_tacexpr.delayed_open_constr_with_bindings_of_sexp);
  }

let ser_wit_tactic = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = Ser_geninterp.Val.sexp_of_t;

    raw_des = Ser_tacexpr.raw_tactic_expr_of_sexp;
    glb_des = Ser_tacexpr.glob_tactic_expr_of_sexp;
    top_des = Ser_geninterp.Val.t_of_sexp;
  }

let ser_wit_ltac = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Ser_tacexpr.raw_tactic_expr_of_sexp;
    glb_des = Ser_tacexpr.glob_tactic_expr_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_quant_hyp =
  Ser_genarg.mk_uniform
    Ser_tactypes.sexp_of_quantified_hypothesis
    Ser_tactypes.quantified_hypothesis_of_sexp

let ser_wit_bindings :
  (Constrexpr.constr_expr Tactypes.bindings,
   Genintern.glob_constr_and_expr Tactypes.bindings,
   EConstr.constr Tactypes.bindings Tactypes.delayed_open)
    Ser_genarg.gen_ser
 = Ser_genarg.{
    raw_ser = Ser_tactypes.sexp_of_bindings Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tactypes.sexp_of_bindings Ser_genintern.sexp_of_glob_constr_and_expr;
    top_ser = Serlib_base.sexp_of_opaque ~typ:"wit_bindings/top";

    raw_des = Ser_tactypes.bindings_of_sexp Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tactypes.bindings_of_sexp Ser_genintern.glob_constr_and_expr_of_sexp;
    top_des = Serlib_base.opaque_of_sexp ~typ:"wit_bindings/top";
  }

let ser_wit_constr_with_bindings :
  (Constrexpr.constr_expr Tactypes.with_bindings,
   Genintern.glob_constr_and_expr Tactypes.with_bindings,
   EConstr.constr Tactypes.with_bindings Tactypes.delayed_open)
    Ser_genarg.gen_ser
 = Ser_genarg.{
    raw_ser = Ser_tactypes.sexp_of_with_bindings Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tactypes.sexp_of_with_bindings Ser_genintern.sexp_of_glob_constr_and_expr;
    top_ser = Serlib_base.sexp_of_opaque ~typ:"wit_constr_with_bindings/top";

    raw_des = Ser_tactypes.with_bindings_of_sexp Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tactypes.with_bindings_of_sexp Ser_genintern.glob_constr_and_expr_of_sexp;
    top_des = Serlib_base.opaque_of_sexp ~typ:"wit_constr_with_bindings/top";
  }

(* G_ltac *)
(* Defined in g_ltac but serialized here *)

let ser_wit_ltac_info =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_int;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = int_of_sexp;
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_production_item =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = Ser_tacentries.(sexp_of_grammar_tactic_prod_item_expr sexp_of_raw_argument);
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = Ser_tacentries.(grammar_tactic_prod_item_expr_of_sexp raw_argument_of_sexp);
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_ltac_production_sep =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_string;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = string_of_sexp;
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_ltac_selector = Ser_genarg.{
    raw_ser = Ser_goal_select.sexp_of_t;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Ser_goal_select.t_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_ltac_tacdef_body = Ser_genarg.{
    raw_ser = Ser_tacexpr.sexp_of_tacdef_body;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Ser_tacexpr.tacdef_body_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_ltac_tactic_level = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_int;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Sexplib.Conv.int_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp;
  }

let ser_wit_ltac_use_default = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_bool;
    glb_ser = Sexplib.Conv.sexp_of_unit;
    top_ser = Sexplib.Conv.sexp_of_unit;

    raw_des = Sexplib.Conv.bool_of_sexp;
    glb_des = Sexplib.Conv.unit_of_sexp;
    top_des = Sexplib.Conv.unit_of_sexp
  }

(* From G_auto *)
let ser_wit_auto_using = Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_list Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Sexplib.Conv.sexp_of_list Ser_genintern.sexp_of_glob_constr_and_expr;
    top_ser = Sexplib.Conv.sexp_of_list Ser_ltac_pretype.sexp_of_closed_glob_constr;

    raw_des = Sexplib.Conv.list_of_sexp Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Sexplib.Conv.list_of_sexp Ser_genintern.glob_constr_and_expr_of_sexp;
    top_des = Sexplib.Conv.list_of_sexp Ser_ltac_pretype.closed_glob_constr_of_sexp;
  }

let ser_wit_hintbases =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_option (sexp_of_list sexp_of_string);
    glb_ser = sexp_of_option (sexp_of_list sexp_of_string);
    top_ser = sexp_of_option (sexp_of_list Ser_hints.sexp_of_hint_db_name);

    raw_des = option_of_sexp (list_of_sexp string_of_sexp);
    glb_des = option_of_sexp (list_of_sexp string_of_sexp);
    top_des = option_of_sexp (list_of_sexp Ser_hints.hint_db_name_of_sexp);
  }

let ser_wit_hintbases_path =
  Ser_genarg.{
    raw_ser = Ser_hints.(sexp_of_hints_path_gen Ser_libnames.sexp_of_qualid);
    glb_ser = Ser_hints.sexp_of_hints_path;
    top_ser = Ser_hints.sexp_of_hints_path;

    raw_des = Ser_hints.(hints_path_gen_of_sexp Ser_libnames.qualid_of_sexp);
    glb_des = Ser_hints.hints_path_of_sexp;
    top_des = Ser_hints.hints_path_of_sexp;
  }

let ser_wit_hintbases_path_atom =
  Ser_genarg.{
    raw_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_libnames.sexp_of_qualid);
    glb_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_names.GlobRef.sexp_of_t);
    top_ser = Ser_hints.(sexp_of_hints_path_atom_gen Ser_names.GlobRef.sexp_of_t);

    raw_des = Ser_hints.(hints_path_atom_gen_of_sexp Ser_libnames.qualid_of_sexp);
    glb_des = Ser_hints.(hints_path_atom_gen_of_sexp Ser_names.GlobRef.t_of_sexp);
    top_des = Ser_hints.(hints_path_atom_gen_of_sexp Ser_names.GlobRef.t_of_sexp);
  }

let ser_wit_opthints =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = sexp_of_option (sexp_of_list sexp_of_string);
    glb_ser = sexp_of_option (sexp_of_list sexp_of_string);
    top_ser = sexp_of_option (sexp_of_list Ser_hints.sexp_of_hint_db_name);

    raw_des = option_of_sexp (list_of_sexp string_of_sexp);
    glb_des = option_of_sexp (list_of_sexp string_of_sexp);
    top_des = option_of_sexp (list_of_sexp Ser_hints.hint_db_name_of_sexp);
  }

(* G_rewrite *)

let ser_wit_binders =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_list Ser_constrexpr.sexp_of_local_binder_expr)
    (list_of_sexp Ser_constrexpr.local_binder_expr_of_sexp)

let ser_wit_glob_constr_with_bindings =
  let open Sexplib.Conv in

  let _sexp_of_interp_sign = Serlib_base.sexp_of_opaque ~typ:"interp_sign" in
  let _interp_sign_of_sexp = Serlib_base.opaque_of_sexp ~typ:"interp_sign" in

  Ser_genarg.{
    raw_ser = Ser_tactypes.sexp_of_with_bindings Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tactypes.sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr;
    top_ser = sexp_of_pair _sexp_of_interp_sign Ser_tactypes.(sexp_of_with_bindings Ser_tacexpr.sexp_of_glob_constr_and_expr);

    raw_des = Ser_tactypes.with_bindings_of_sexp Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tactypes.with_bindings_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp;
    top_des = pair_of_sexp _interp_sign_of_sexp Ser_tactypes.(with_bindings_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp)
  }

let ser_wit_rewstrategy =

  Ser_genarg.{
    raw_ser = Ser_rewrite.sexp_of_strategy_ast Ser_constrexpr.sexp_of_constr_expr Ser_tacexpr.sexp_of_raw_red_expr;
    glb_ser = Ser_rewrite.sexp_of_strategy_ast Ser_tacexpr.sexp_of_glob_constr_and_expr Ser_tacexpr.sexp_of_raw_red_expr;
    top_ser = Serlib_base.sexp_of_opaque ~typ:"wit_rewstrategy/top";

    raw_des = Ser_rewrite.strategy_ast_of_sexp Ser_constrexpr.constr_expr_of_sexp Ser_tacexpr.raw_red_expr_of_sexp;
    glb_des = Ser_rewrite.strategy_ast_of_sexp Ser_tacexpr.glob_constr_and_expr_of_sexp Ser_tacexpr.raw_red_expr_of_sexp;
    top_des = Serlib_base.opaque_of_sexp ~typ:"wit_rewstrategy/top";

  }

let ser_wit_debug =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform sexp_of_bool bool_of_sexp

let ser_wit_eauto_search_strategy =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_option Ser_class_tactics.sexp_of_search_strategy)
    (option_of_sexp Ser_class_tactics.search_strategy_of_sexp)

let ser_wit_withtac =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_option Ser_tacexpr.sexp_of_raw_tactic_expr)
    (option_of_sexp Ser_tacexpr.raw_tactic_expr_of_sexp)

(* extraargs *)

open Sexplib.Conv

module Names = Ser_names
module Locus = Ser_locus

type 'a gen_place =
  [%import: 'a Extraargs.gen_place]
  [@@deriving sexp]

type loc_place =
  [%import: Extraargs.loc_place]
  [@@deriving sexp]

type place =
  [%import: Extraargs.place]
  [@@deriving sexp]

let ser_wit_hloc =
  Ser_genarg.{
    raw_ser = sexp_of_loc_place
  ; glb_ser = sexp_of_loc_place
  ; top_ser = sexp_of_place

  ; raw_des = loc_place_of_sexp
  ; glb_des = loc_place_of_sexp
  ; top_des = place_of_sexp
  }

let ser_wit_lglob =
  Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr
  ; glb_ser = Ser_genintern.sexp_of_glob_constr_and_expr
  ; top_ser = sexp_of_pair Ser_geninterp.sexp_of_interp_sign Ser_glob_term.sexp_of_glob_constr

  ; raw_des = Ser_constrexpr.constr_expr_of_sexp
  ; glb_des = Ser_genintern.glob_constr_and_expr_of_sexp
  ; top_des = pair_of_sexp Ser_geninterp.interp_sign_of_sexp Ser_glob_term.glob_constr_of_sexp
  }

let ser_wit_orient =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform sexp_of_bool bool_of_sexp

let ser_wit_rename =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform
    (sexp_of_pair Ser_names.Id.sexp_of_t Ser_names.Id.sexp_of_t)
    (pair_of_sexp Ser_names.Id.t_of_sexp Ser_names.Id.t_of_sexp)

let ser_wit_natural =
  let open Sexplib.Conv in
  Ser_genarg.mk_uniform sexp_of_int int_of_sexp

let ser_wit_lconstr : (Constrexpr.constr_expr, Ltac_plugin.Tacexpr.glob_constr_and_expr, EConstr.t) Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_constr_and_expr;
    top_ser = Ser_eConstr.sexp_of_t;

    raw_des = Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tacexpr.glob_constr_and_expr_of_sexp;
    top_des = Ser_eConstr.t_of_sexp;
  }

let ser_wit_casted_constr :
  (Constrexpr.constr_expr, Ltac_plugin.Tacexpr.glob_constr_and_expr, EConstr.t) Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_tacexpr.sexp_of_glob_constr_and_expr;
    top_ser = Ser_eConstr.sexp_of_t;

    raw_des = Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_tacexpr.glob_constr_and_expr_of_sexp;
    top_des = Ser_eConstr.t_of_sexp;
  }

let ser_wit_in_clause :
  (Names.lident Locus.clause_expr, Names.lident Locus.clause_expr, Names.Id.t Locus.clause_expr) Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = Ser_locus.sexp_of_clause_expr Ser_names.sexp_of_lident;
    glb_ser = Ser_locus.sexp_of_clause_expr Ser_names.sexp_of_lident;
    top_ser = Ser_locus.sexp_of_clause_expr Ser_names.Id.sexp_of_t;

    raw_des = Ser_locus.clause_expr_of_sexp Ser_names.lident_of_sexp;
    glb_des = Ser_locus.clause_expr_of_sexp Ser_names.lident_of_sexp;
    top_des = Ser_locus.clause_expr_of_sexp Ser_names.Id.t_of_sexp;
  }

let ser_wit_by_arg_tac :
  (Tacexpr.raw_tactic_expr option, Tacexpr.glob_tactic_expr option, Tacinterp.value option) Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = Sexplib.Conv.sexp_of_option Ser_tacexpr.sexp_of_raw_tactic_expr;
    glb_ser = Sexplib.Conv.sexp_of_option Ser_tacexpr.sexp_of_glob_tactic_expr;
    top_ser = Sexplib.Conv.sexp_of_option Ser_geninterp.Val.sexp_of_t;

    raw_des = Sexplib.Conv.option_of_sexp Ser_tacexpr.raw_tactic_expr_of_sexp;
    glb_des = Sexplib.Conv.option_of_sexp Ser_tacexpr.glob_tactic_expr_of_sexp;
    top_des = Sexplib.Conv.option_of_sexp Ser_geninterp.Val.t_of_sexp;
  }

let ser_wit_retroknowledge_field =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = Ser_retroknowledge.sexp_of_field;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = Ser_retroknowledge.field_of_sexp;
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

let ser_wit_occurences =
  let open Sexplib.Conv in
  Ser_genarg.{
    raw_ser = Ser_locus.sexp_of_or_var (sexp_of_list sexp_of_int);
    glb_ser = Ser_locus.sexp_of_or_var (sexp_of_list sexp_of_int);
    top_ser = sexp_of_list sexp_of_int;

    raw_des = Ser_locus.or_var_of_sexp (list_of_sexp int_of_sexp);
    glb_des = Ser_locus.or_var_of_sexp (list_of_sexp int_of_sexp);
    top_des = list_of_sexp int_of_sexp;
  }

let register () =

  Ser_genarg.register_genser Tacarg.wit_bindings ser_wit_bindings;
  Ser_genarg.register_genser Tacarg.wit_constr_with_bindings      ser_wit_constr_with_bindings;
  Ser_genarg.register_genser Tacarg.wit_open_constr_with_bindings ser_wit_constr_with_bindings;
  Ser_genarg.register_genser Tacarg.wit_destruction_arg ser_wit_destruction_arg;
  Ser_genarg.register_genser Tacarg.wit_intropattern  ser_wit_intropattern;
  (* Ser_genarg.register_genser Tacarg.wit_intro_pattern ser_wit_intropattern; *)
  Ser_genarg.register_genser Tacarg.wit_ltac ser_wit_ltac;
  Ser_genarg.register_genser Tacarg.wit_quant_hyp ser_wit_quant_hyp;
  (* Ser_genarg.register_genser Tacarg.wit_quantified_hypothesis ser_wit_quant_hyp; *)
  Ser_genarg.register_genser Tacarg.wit_tactic ser_wit_tactic;

  Ser_genarg.register_genser G_ltac.wit_ltac_info ser_wit_ltac_info;
  Ser_genarg.register_genser G_ltac.wit_ltac_production_item ser_wit_production_item;
  Ser_genarg.register_genser G_ltac.wit_ltac_production_sep ser_wit_ltac_production_sep;
  Ser_genarg.register_genser G_ltac.wit_ltac_selector ser_wit_ltac_selector;
  Ser_genarg.register_genser G_ltac.wit_ltac_tacdef_body ser_wit_ltac_tacdef_body;
  Ser_genarg.register_genser G_ltac.wit_ltac_tactic_level ser_wit_ltac_tactic_level;
  Ser_genarg.register_genser G_ltac.wit_ltac_use_default ser_wit_ltac_use_default;

  Ser_genarg.register_genser G_auto.wit_auto_using ser_wit_auto_using;
  Ser_genarg.register_genser G_auto.wit_hintbases ser_wit_hintbases;
  Ser_genarg.register_genser G_auto.wit_hints_path ser_wit_hintbases_path;
  Ser_genarg.register_genser G_auto.wit_hints_path_atom ser_wit_hintbases_path_atom;
  Ser_genarg.register_genser G_auto.wit_opthints ser_wit_opthints;

  Ser_genarg.register_genser G_rewrite.wit_binders ser_wit_binders;
  Ser_genarg.register_genser G_rewrite.wit_glob_constr_with_bindings ser_wit_glob_constr_with_bindings;
  Ser_genarg.register_genser G_rewrite.wit_rewstrategy ser_wit_rewstrategy;

  Ser_genarg.register_genser G_class.wit_debug ser_wit_debug;
  Ser_genarg.register_genser G_class.wit_eauto_search_strategy ser_wit_eauto_search_strategy;

  Ser_genarg.register_genser G_obligations.wit_withtac ser_wit_withtac;

  Ser_genarg.register_genser Extraargs.wit_by_arg_tac ser_wit_by_arg_tac;
  Ser_genarg.register_genser Extraargs.wit_casted_constr ser_wit_casted_constr;
  Ser_genarg.register_genser Extraargs.wit_glob ser_wit_lglob;
  Ser_genarg.register_genser Extraargs.wit_hloc ser_wit_hloc;
  Ser_genarg.register_genser Extraargs.wit_in_clause ser_wit_in_clause;
  Ser_genarg.register_genser Extraargs.wit_lconstr ser_wit_lconstr;
  Ser_genarg.register_genser Extraargs.wit_lglob ser_wit_lglob;
  Ser_genarg.register_genser Extraargs.wit_natural ser_wit_natural;
  Ser_genarg.register_genser Extraargs.wit_orient ser_wit_orient;
  Ser_genarg.register_genser Extraargs.wit_occurrences ser_wit_occurences;
  Ser_genarg.register_genser Extraargs.wit_rename ser_wit_rename;
  Ser_genarg.register_genser Extraargs.wit_retroknowledge_field ser_wit_retroknowledge_field;
  Ser_genarg.register_genser Extraargs.wit_test_lpar_id_colon Ser_genarg.(mk_uniform sexp_of_unit unit_of_sexp);

  ()

let _ = register ()
