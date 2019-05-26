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

open Sexplib
open Ltac_plugin

type direction_flag = bool
val direction_flag_of_sexp : Sexp.t -> direction_flag
val sexp_of_direction_flag : direction_flag -> Sexp.t

type lazy_flag = Tacexpr.lazy_flag = General | Select | Once
val lazy_flag_of_sexp : Sexp.t -> lazy_flag
val sexp_of_lazy_flag : lazy_flag -> Sexp.t

type global_flag = Tacexpr.global_flag = TacGlobal | TacLocal
val global_flag_of_sexp : Sexp.t -> global_flag
val sexp_of_global_flag : global_flag -> Sexp.t

type evars_flag = bool
val evars_flag_of_sexp : Sexp.t -> evars_flag
val sexp_of_evars_flag : evars_flag -> Sexp.t

type rec_flag = bool
val rec_flag_of_sexp : Sexp.t -> rec_flag
val sexp_of_rec_flag : rec_flag -> Sexp.t

type advanced_flag = bool
val advanced_flag_of_sexp : Sexp.t -> advanced_flag
val sexp_of_advanced_flag : advanced_flag -> Sexp.t

type letin_flag = bool
val letin_flag_of_sexp : Sexp.t -> letin_flag
val sexp_of_letin_flag : letin_flag -> Sexp.t

type clear_flag = bool option
val clear_flag_of_sexp : Sexp.t -> clear_flag
val sexp_of_clear_flag : clear_flag -> Sexp.t

(* type debug = Tacexpr.debug = Debug | Info | Off *)
(* val debug_of_sexp : Sexp.t -> debug *)
(* val sexp_of_debug : debug -> Sexp.t *)

(* type goal_selector = Tacexpr.goal_selector *)
(* val goal_selector_of_sexp : Sexp.t -> goal_selector *)
(* val sexp_of_goal_selector : goal_selector -> Sexp.t *)

type ('c, 'd, 'id) inversion_strength = ('c, 'd, 'id) Tacexpr.inversion_strength

val inversion_strength_of_sexp :
  (Sexp.t -> 'c) ->
  (Sexp.t -> 'd) ->
  (Sexp.t -> 'id) ->
  Sexp.t -> ('c, 'd, 'id) inversion_strength

val sexp_of_inversion_strength :
  ('c -> Sexp.t) ->
  ('d -> Sexp.t) ->
  ('id -> Sexp.t) ->
  ('c, 'd, 'id) inversion_strength -> Sexp.t

type ('a, 'b) location =
  ('a, 'b) Tacexpr.location =
    HypLocation of 'a
  | ConclLocation of 'b

val location_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) -> Sexp.t -> ('a, 'b) location

val sexp_of_location :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) -> ('a, 'b) location -> Sexp.t

type 'id message_token = 'id Tacexpr.message_token

val message_token_of_sexp :
  (Sexp.t -> 'id) -> Sexp.t -> 'id message_token

val sexp_of_message_token :
  ('id -> Sexp.t) -> 'id message_token -> Sexp.t

type ('dconstr, 'id) induction_clause = ('dconstr, 'id) Tacexpr.induction_clause

val induction_clause_of_sexp :
  (Sexp.t -> 'dconstr) ->
  (Sexp.t -> 'id) ->
  Sexp.t -> ('dconstr, 'id) induction_clause

val sexp_of_induction_clause :
  ('dconstr -> Sexp.t) ->
  ('id -> Sexp.t) ->
  ('dconstr, 'id) induction_clause -> Sexp.t


type ('constr, 'dconstr, 'id) induction_clause_list =
  ('constr, 'dconstr, 'id) Tacexpr.induction_clause_list

val induction_clause_list_of_sexp :
  (Sexp.t -> 'constr) ->
  (Sexp.t -> 'dconstr) ->
  (Sexp.t -> 'id) ->
  Sexp.t -> ('constr, 'dconstr, 'id) induction_clause_list

val sexp_of_induction_clause_list :
  ('constr -> Sexp.t) ->
  ('dconstr -> Sexp.t) ->
  ('id -> Sexp.t) ->
  ('constr, 'dconstr, 'id) induction_clause_list -> Sexp.t

type 'a with_bindings_arg = 'a Tacexpr.with_bindings_arg

val with_bindings_arg_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a with_bindings_arg
val sexp_of_with_bindings_arg : ('a -> Sexp.t) -> 'a with_bindings_arg -> Sexp.t

(* type multi = Tacexpr.multi *)
(* val multi_of_sexp : Sexp.t -> multi *)
(* val sexp_of_multi : multi -> Sexp.t *)

type 'a match_pattern = 'a Tacexpr.match_pattern

val match_pattern_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a match_pattern
val sexp_of_match_pattern : ('a -> Sexp.t) -> 'a match_pattern -> Sexp.t

type 'a match_context_hyps = 'a Tacexpr.match_context_hyps

val match_context_hyps_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a match_context_hyps
val sexp_of_match_context_hyps : ('a -> Sexp.t) -> 'a match_context_hyps -> Sexp.t

type ('a, 't) match_rule = ('a, 't) Tacexpr.match_rule

val match_rule_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 't) -> Sexp.t -> ('a, 't) match_rule
val sexp_of_match_rule :
  ('a -> Sexp.t) ->
  ('t -> Sexp.t) -> ('a, 't) match_rule -> Sexp.t

type ml_tactic_name = Tacexpr.ml_tactic_name

val ml_tactic_name_of_sexp : Sexp.t -> ml_tactic_name
val sexp_of_ml_tactic_name : ml_tactic_name -> Sexp.t

type 'd gen_atomic_tactic_expr = 'd Tacexpr.gen_atomic_tactic_expr

val sexp_of_gen_atomic_tactic_expr :
  ('a -> Sexplib.Sexp.t) ->
  ('c -> Sexplib.Sexp.t) ->
  ('d -> Sexplib.Sexp.t) ->
  ('e -> Sexplib.Sexp.t) ->
  ('f -> Sexplib.Sexp.t) ->
  ('g -> Sexplib.Sexp.t) ->
  ('h -> Sexplib.Sexp.t) ->
  ('i -> Sexplib.Sexp.t) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_atomic_tactic_expr -> Sexplib.Sexp.t
val sexp_of_gen_tactic_expr :
  ('a -> Sexplib.Sexp.t) ->
  ('c -> Sexplib.Sexp.t) ->
  ('d -> Sexplib.Sexp.t) ->
  ('e -> Sexplib.Sexp.t) ->
  ('f -> Sexplib.Sexp.t) ->
  ('g -> Sexplib.Sexp.t) ->
  ('h -> Sexplib.Sexp.t) ->
  ('i -> Sexplib.Sexp.t) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_tactic_expr -> Sexplib.Sexp.t
val sexp_of_gen_tactic_arg :
  ('a -> Sexplib.Sexp.t) ->
  ('c -> Sexplib.Sexp.t) ->
  ('d -> Sexplib.Sexp.t) ->
  ('e -> Sexplib.Sexp.t) ->
  ('f -> Sexplib.Sexp.t) ->
  ('g -> Sexplib.Sexp.t) ->
  ('h -> Sexplib.Sexp.t) ->
  ('i -> Sexplib.Sexp.t) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_tactic_arg -> Sexplib.Sexp.t
val sexp_of_gen_fun_ast :
  ('a -> Sexplib.Sexp.t) ->
  ('c -> Sexplib.Sexp.t) ->
  ('d -> Sexplib.Sexp.t) ->
  ('e -> Sexplib.Sexp.t) ->
  ('f -> Sexplib.Sexp.t) ->
  ('g -> Sexplib.Sexp.t) ->
  ('h -> Sexplib.Sexp.t) ->
  ('i -> Sexplib.Sexp.t) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_tactic_fun_ast -> Sexplib.Sexp.t

val gen_atomic_tactic_expr_of_sexp :
  Sexplib.Sexp.t ->
  (Sexplib.Sexp.t -> 'a) ->
  (Sexplib.Sexp.t -> 'c) ->
  (Sexplib.Sexp.t -> 'd) ->
  (Sexplib.Sexp.t -> 'e) ->
  (Sexplib.Sexp.t -> 'f) ->
  (Sexplib.Sexp.t -> 'g) ->
  (Sexplib.Sexp.t -> 'h) ->
  (Sexplib.Sexp.t -> 'i) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_atomic_tactic_expr

val gen_tactic_expr_of_sexp :
  Sexplib.Sexp.t ->
  (Sexplib.Sexp.t -> 'a) ->
  (Sexplib.Sexp.t -> 'c) ->
  (Sexplib.Sexp.t -> 'd) ->
  (Sexplib.Sexp.t -> 'e) ->
  (Sexplib.Sexp.t -> 'f) ->
  (Sexplib.Sexp.t -> 'g) ->
  (Sexplib.Sexp.t -> 'h) ->
  (Sexplib.Sexp.t -> 'i) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_tactic_expr

val gen_tactic_arg_of_sexp :
  Sexplib.Sexp.t ->
  (Sexplib.Sexp.t -> 'a) ->
  (Sexplib.Sexp.t -> 'c) ->
  (Sexplib.Sexp.t -> 'd) ->
  (Sexplib.Sexp.t -> 'e) ->
  (Sexplib.Sexp.t -> 'f) ->
  (Sexplib.Sexp.t -> 'g) ->
  (Sexplib.Sexp.t -> 'h) ->
  (Sexplib.Sexp.t -> 'i) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a  >
  Tacexpr.gen_tactic_arg

val gen_fun_ast_of_sexp :
  Sexplib.Sexp.t ->
  (Sexplib.Sexp.t -> 'a) ->
  (Sexplib.Sexp.t -> 'c) ->
  (Sexplib.Sexp.t -> 'd) ->
  (Sexplib.Sexp.t -> 'e) ->
  (Sexplib.Sexp.t -> 'f) ->
  (Sexplib.Sexp.t -> 'g) ->
  (Sexplib.Sexp.t -> 'h) ->
  (Sexplib.Sexp.t -> 'i) ->
  < constant : 'e; dterm : 'c; level : 'i; name : 'g; pattern : 'd;
    reference : 'f; tacexpr : 'h; term : 'a >
  Tacexpr.gen_tactic_fun_ast

type glob_tactic_expr = Tacexpr.glob_tactic_expr
val glob_tactic_expr_of_sexp : Sexp.t -> glob_tactic_expr
val sexp_of_glob_tactic_expr : glob_tactic_expr -> Sexp.t

type glob_atomic_tactic_expr = Tacexpr.glob_atomic_tactic_expr
val glob_atomic_tactic_expr_of_sexp : Sexp.t -> glob_atomic_tactic_expr
val sexp_of_glob_atomic_tactic_expr : glob_atomic_tactic_expr -> Sexp.t

type raw_tactic_expr = Tacexpr.raw_tactic_expr
val raw_tactic_expr_of_sexp : Sexp.t -> raw_tactic_expr
val sexp_of_raw_tactic_expr : raw_tactic_expr -> Sexp.t

type raw_atomic_tactic_expr = Tacexpr.raw_atomic_tactic_expr
val raw_atomic_tactic_expr_of_sexp : Sexp.t -> raw_atomic_tactic_expr
val sexp_of_raw_atomic_tactic_expr : raw_atomic_tactic_expr -> Sexp.t

type atomic_tactic_expr = Tacexpr.atomic_tactic_expr
val atomic_tactic_expr_of_sexp : Sexp.t -> atomic_tactic_expr
val sexp_of_atomic_tactic_expr : atomic_tactic_expr -> Sexp.t

type raw_red_expr = Tacexpr.raw_red_expr
val raw_red_expr_of_sexp : Sexp.t -> raw_red_expr
val sexp_of_raw_red_expr : raw_red_expr -> Sexp.t

type tacdef_body = Tacexpr.tacdef_body
val tacdef_body_of_sexp : Sexp.t -> tacdef_body
val sexp_of_tacdef_body : tacdef_body -> Sexp.t

type glob_constr_and_expr = Tacexpr.glob_constr_and_expr
val glob_constr_and_expr_of_sexp : Sexp.t -> glob_constr_and_expr
val sexp_of_glob_constr_and_expr : glob_constr_and_expr -> Sexp.t

type 'a delayed_open = 'a Tacexpr.delayed_open
val delayed_open_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a delayed_open
val sexp_of_delayed_open : ('a -> Sexp.t) -> 'a delayed_open -> Sexp.t

type delayed_open_constr_with_bindings = Tacexpr.delayed_open_constr_with_bindings
val delayed_open_constr_with_bindings_of_sexp : Sexp.t -> delayed_open_constr_with_bindings
val sexp_of_delayed_open_constr_with_bindings : delayed_open_constr_with_bindings -> Sexp.t

type delayed_open_constr = Tacexpr.delayed_open_constr
val delayed_open_constr_of_sexp : Sexp.t -> delayed_open_constr
val sexp_of_delayed_open_constr : delayed_open_constr -> Sexp.t

type intro_pattern = Tacexpr.intro_pattern
val intro_pattern_of_sexp : Sexp.t -> intro_pattern
val sexp_of_intro_pattern : intro_pattern -> Sexp.t
