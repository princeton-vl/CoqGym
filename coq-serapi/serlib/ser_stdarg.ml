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

module Names      = Ser_names

type 'a and_short_name =
  [%import: 'a Stdarg.and_short_name]
  [@@deriving sexp]

let ser_wit_unit   = Ser_genarg.mk_uniform sexp_of_unit unit_of_sexp
let ser_wit_bool   = Ser_genarg.mk_uniform sexp_of_bool bool_of_sexp
let ser_wit_int    = Ser_genarg.mk_uniform sexp_of_int int_of_sexp
let ser_wit_string = Ser_genarg.mk_uniform sexp_of_string string_of_sexp
let ser_wit_pre_ident = Ser_genarg.mk_uniform sexp_of_string string_of_sexp

let ser_wit_int_or_var = Ser_genarg.{
    raw_ser = Ser_locus.sexp_of_or_var sexp_of_int;
    glb_ser = Ser_locus.sexp_of_or_var sexp_of_int;
    top_ser = sexp_of_int;

    raw_des = Ser_locus.or_var_of_sexp int_of_sexp;
    glb_des = Ser_locus.or_var_of_sexp int_of_sexp;
    top_des = int_of_sexp;
  }

let ser_wit_ident  = Ser_genarg.mk_uniform Ser_names.Id.sexp_of_t Ser_names.Id.t_of_sexp

let ser_wit_var = Ser_genarg.{
    raw_ser = Ser_names.sexp_of_lident;
    glb_ser = Ser_names.sexp_of_lident;
    top_ser = Ser_names.Id.sexp_of_t;

    raw_des = Ser_names.lident_of_sexp;
    glb_des = Ser_names.lident_of_sexp;
    top_des = Ser_names.Id.t_of_sexp;
  }

let ser_wit_ref = Ser_genarg.{
    raw_ser = Ser_libnames.sexp_of_qualid;
    glb_ser = Ser_locus.sexp_of_or_var Ser_loc.(sexp_of_located Ser_names.GlobRef.sexp_of_t);
    top_ser = Ser_names.GlobRef.sexp_of_t;

    raw_des = Ser_libnames.qualid_of_sexp;
    glb_des = Ser_locus.or_var_of_sexp Ser_loc.(located_of_sexp Ser_names.GlobRef.t_of_sexp);
    top_des = Ser_names.GlobRef.t_of_sexp;
  }

let ser_wit_sort_family = Ser_genarg.{
    raw_ser = Ser_sorts.sexp_of_family;
    glb_ser = sexp_of_unit;
    top_ser = sexp_of_unit;

    raw_des = Ser_sorts.family_of_sexp;
    glb_des = unit_of_sexp;
    top_des = unit_of_sexp;
  }

(* let ser_ref  *)

let ser_wit_constr = Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_genintern.sexp_of_glob_constr_and_expr;
    top_ser = Ser_eConstr.sexp_of_t;

    raw_des = Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_genintern.glob_constr_and_expr_of_sexp;
    top_des = Ser_eConstr.t_of_sexp;
  }

let ser_wit_uconstr = Ser_genarg.{
    raw_ser = Ser_constrexpr.sexp_of_constr_expr;
    glb_ser = Ser_genintern.sexp_of_glob_constr_and_expr;
    top_ser = Ser_ltac_pretype.sexp_of_closed_glob_constr;

    raw_des = Ser_constrexpr.constr_expr_of_sexp;
    glb_des = Ser_genintern.glob_constr_and_expr_of_sexp;
    top_des = Ser_ltac_pretype.closed_glob_constr_of_sexp;
  }

type wrd_h1 =
  (Ser_constrexpr.constr_expr,
   Ser_libnames.qualid Ser_constrexpr.or_by_notation,
   Ser_constrexpr.constr_expr)
    Ser_genredexpr.red_expr_gen
  [@@deriving sexp]

type wrd_h2 =
  (Ser_genintern.glob_constr_and_expr,
   Ser_names.evaluable_global_reference and_short_name Ser_locus.or_var,
   Ser_genintern.glob_constr_pattern_and_expr)
    Ser_genredexpr.red_expr_gen
  [@@deriving sexp]

type wrd_h3 =
  (Ser_eConstr.constr,
   Ser_names.evaluable_global_reference,
   Ser_pattern.constr_pattern)
    Ser_genredexpr.red_expr_gen
  [@@deriving sexp]

let ser_wit_red_expr = Ser_genarg.{
    raw_ser = sexp_of_wrd_h1;
    glb_ser = sexp_of_wrd_h2;
    top_ser = sexp_of_wrd_h3;

    raw_des = wrd_h1_of_sexp;
    glb_des = wrd_h2_of_sexp;
    top_des = wrd_h3_of_sexp;
  }

let ser_wit_clause_dft_concl = Ser_genarg.{
    raw_ser = Ser_locus.sexp_of_clause_expr Ser_names.sexp_of_lident;
    glb_ser = Ser_locus.sexp_of_clause_expr Ser_names.sexp_of_lident;
    top_ser = Ser_locus.sexp_of_clause_expr Ser_names.Id.sexp_of_t;

    raw_des = Ser_locus.clause_expr_of_sexp Ser_names.lident_of_sexp;
    glb_des = Ser_locus.clause_expr_of_sexp Ser_names.lident_of_sexp;
    top_des = Ser_locus.clause_expr_of_sexp Ser_names.Id.t_of_sexp;
  }

let register () =

  Ser_genarg.register_genser Stdarg.wit_bool ser_wit_bool;
  Ser_genarg.register_genser Stdarg.wit_clause_dft_concl ser_wit_clause_dft_concl;
  Ser_genarg.register_genser Stdarg.wit_constr ser_wit_constr;
  (* Ser_genarg.register_genser Stdarg.wit_global ser_wit_ref; *)
  Ser_genarg.register_genser Stdarg.wit_ident ser_wit_ident;
  Ser_genarg.register_genser Stdarg.wit_int ser_wit_int;
  Ser_genarg.register_genser Stdarg.wit_int_or_var ser_wit_int_or_var;
  (* Ser_genarg.register_genser Stdarg.wit_integer ser_wit_int; *)
  Ser_genarg.register_genser Stdarg.wit_open_constr ser_wit_constr;
  Ser_genarg.register_genser Stdarg.wit_pre_ident ser_wit_pre_ident;
  (* Ser_genarg.register_genser Stdarg.wit_preident ser_wit_pre_ident; *)
  Ser_genarg.register_genser Stdarg.wit_red_expr ser_wit_red_expr;
  (* Ser_genarg.register_genser Stdarg.wit_redexpr ser_wit_red_expr; *)
  Ser_genarg.register_genser Stdarg.wit_ref ser_wit_ref;
  (* Ser_genarg.register_genser Stdarg.wit_reference ser_wit_ref; *)
  Ser_genarg.register_genser Stdarg.wit_sort_family ser_wit_sort_family;
  Ser_genarg.register_genser Stdarg.wit_string ser_wit_string;
  Ser_genarg.register_genser Stdarg.wit_uconstr ser_wit_uconstr;
  Ser_genarg.register_genser Stdarg.wit_unit ser_wit_unit;
  Ser_genarg.register_genser Stdarg.wit_var ser_wit_var;

  ()

let _ = register ()
