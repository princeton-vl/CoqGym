(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib
open Sexplib.Std

module Loc       = Ser_loc
module CAst      = Ser_cAst
module Names     = Ser_names
module Locus     = Ser_locus
module Constr    = Ser_constr
module EConstr   = Ser_eConstr
module Nametab   = Ser_nametab
module Constr_matching = Ser_constr_matching
module Libnames   = Ser_libnames
module Namegen    = Ser_namegen
module Genarg     = Ser_genarg
module Stdarg     = Ser_stdarg
module Genredexpr = Ser_genredexpr
module Genintern  = Ser_genintern
module Goal_select = Ser_goal_select
module Pattern    = Ser_pattern
module Constrexpr = Ser_constrexpr
module Vernacexpr = Ser_vernacexpr
module Tactypes   = Ser_tactypes
module Tactics    = Ser_tactics
module Equality   = Ser_equality
module Inv        = Ser_inv

open Ltac_plugin

type direction_flag =
  [%import: Tacexpr.direction_flag]
  [@@deriving sexp]

type lazy_flag =
  [%import: Tacexpr.lazy_flag]
  [@@deriving sexp]

type global_flag =
  [%import: Tacexpr.global_flag]
  [@@deriving sexp]

type evars_flag =
  [%import: Tacexpr.evars_flag]
  [@@deriving sexp]

type rec_flag =
  [%import: Tacexpr.rec_flag]
  [@@deriving sexp]

type advanced_flag =
  [%import: Tacexpr.advanced_flag]
  [@@deriving sexp]

type letin_flag =
  [%import: Tacexpr.letin_flag]
  [@@deriving sexp]

type clear_flag =
  [%import: Tacexpr.clear_flag]
  [@@deriving sexp]

type ltac_constant =
  [%import: Tacexpr.ltac_constant]
  [@@deriving sexp]

type ('c,'d,'id) inversion_strength =
  [%import: ('c,'d,'id) Tacexpr.inversion_strength]
  [@@deriving sexp]

type ('a,'b) location =
  [%import: ('a, 'b) Tacexpr.location]
  [@@deriving sexp]

type 'id message_token =
  [%import: ('id) Tacexpr.message_token]
  [@@deriving sexp]

type ('dconstr,'id) induction_clause =
  [%import: ('dconstr,'id) Tacexpr.induction_clause]
  [@@deriving sexp]

type ('constr,'dconstr,'id) induction_clause_list =
  [%import: ('constr,'dconstr,'id) Tacexpr.induction_clause_list]
  [@@deriving sexp]

type 'a with_bindings_arg =
  [%import: 'a Tacexpr.with_bindings_arg]
  [@@deriving sexp]

type 'a match_pattern =
  [%import: 'a Tacexpr.match_pattern]
  [@@deriving sexp]

type 'a match_context_hyps =
  [%import: 'a Tacexpr.match_context_hyps]
  [@@deriving sexp]

type ('a,'t) match_rule =
  [%import: ('a, 't) Tacexpr.match_rule]
  [@@deriving sexp]

type ml_tactic_name =
  [%import: Tacexpr.ml_tactic_name]
  [@@deriving sexp]

type ml_tactic_entry =
  [%import: Tacexpr.ml_tactic_entry]
  [@@deriving sexp]

(* type dyn = Ser_Dyn [@@deriving sexp] *)
(* let to_dyn _   = Ser_Dyn *)
(* let from_dyn _ = fst (Dyn.create "dyn_tac") 0 *)

(* This is beyond import and sexp for the moment, see:
 * https://github.com/janestreet/ppx_sexp_conv/issues/6
 *)
(* We thus iso-project the tactic definition in a virtually identical copy (but for the Dyn) *)
module ITac = struct

type ('trm, 'dtrm, 'pat, 'cst, 'ref, 'nam, 'tacexpr, 'lev) gen_atomic_tactic_expr =
  | TacIntroPattern of evars_flag * 'dtrm Tactypes.intro_pattern_expr CAst.t list
  | TacApply of advanced_flag * evars_flag * 'trm with_bindings_arg list *
      ('nam * 'dtrm Tactypes.intro_pattern_expr CAst.t option) option
  | TacElim of evars_flag * 'trm with_bindings_arg * 'trm Tactypes.with_bindings option
  | TacCase of evars_flag * 'trm with_bindings_arg
  | TacMutualFix of Names.Id.t * int * (Names.Id.t * int * 'trm) list
  | TacMutualCofix of Names.Id.t * (Names.Id.t * 'trm) list
  | TacAssert of
      evars_flag * bool * 'tacexpr option option *
      'dtrm Tactypes.intro_pattern_expr CAst.t option * 'trm
  | TacGeneralize of ('trm Locus.with_occurrences * Names.Name.t) list
  | TacLetTac of evars_flag * Names.Name.t * 'trm * 'nam Locus.clause_expr * letin_flag *
      Namegen.intro_pattern_naming_expr CAst.t option
  | TacInductionDestruct of
      rec_flag * evars_flag * ('trm,'dtrm,'nam) induction_clause_list
  | TacReduce of ('trm,'cst,'pat) Genredexpr.red_expr_gen * 'nam Locus.clause_expr
  | TacChange of 'pat option * 'dtrm * 'nam Locus.clause_expr
  | TacRewrite of evars_flag *
      (bool * Equality.multi * 'dtrm with_bindings_arg) list * 'nam Locus.clause_expr *
      'tacexpr option
  | TacInversion of ('trm,'dtrm,'nam) inversion_strength * Tactypes.quantified_hypothesis

and ('trm, 'dtrm, 'pat, 'cst, 'ref, 'nam, 'tacexpr, 'lev) gen_tactic_arg =
  | TacGeneric     of 'lev Genarg.generic_argument
  | ConstrMayEval  of ('trm,'cst,'pat) Genredexpr.may_eval
  | Reference      of 'ref
  | TacCall        of ('ref *
      ('trm, 'dtrm, 'pat, 'cst, 'ref, 'nam, 'tacexpr, 'lev) gen_tactic_arg list) Loc.located
  | TacFreshId of string Locus.or_var list
  | Tacexp of 'tacexpr
  | TacPretype of 'trm
  | TacNumgoals
and ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr =
  | TacAtom of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_atomic_tactic_expr Loc.located
  | TacThen of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacDispatch of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacExtendTac of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array
  | TacThens of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacThens3parts of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr array
  | TacFirst of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacComplete of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacSolve of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr list
  | TacTry of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacOr of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacOnce of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacExactlyOnce of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacIfThenCatch of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacOrelse of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacDo of int Locus.or_var * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacTimeout of int Locus.or_var * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacTime of string option * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacRepeat of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacProgress of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacShowHyps of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacAbstract of
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr * Names.Id.t option
  | TacId of 'n message_token list
  | TacFail of global_flag * int Locus.or_var * 'n message_token list
  | TacInfo of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacLetIn of rec_flag *
      (Names.lname * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg) list *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacMatch of lazy_flag *
      ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr *
      ('p,('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag *
      ('p,('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr) match_rule list
  | TacFun of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_fun_ast
  | TacArg of ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg Loc.located
  | TacSelect of Goal_select.t * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
  | TacML     of (ml_tactic_entry * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg list) Loc.located
  | TacAlias  of (Names.KerName.t * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_arg list) Loc.located

and ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_fun_ast =
    Names.Name.t list * ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) gen_tactic_expr
   [@@deriving sexp]

end

let rec _gen_atom_tactic_expr_put (t : 'a Tacexpr.gen_atomic_tactic_expr) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_atomic_tactic_expr = match t with
  | Tacexpr.TacIntroPattern(a,b)         -> ITac.TacIntroPattern(a,b)
  | Tacexpr.TacApply (a,b,c,d)           -> ITac.TacApply (a,b,c,d)
  | Tacexpr.TacElim (a,b,c)              -> ITac.TacElim (a,b,c)
  | Tacexpr.TacCase (a,b)                -> ITac.TacCase (a,b)
  | Tacexpr.TacMutualFix (a,b,c)         -> ITac.TacMutualFix (a,b,c)
  | Tacexpr.TacMutualCofix (a,b)         -> ITac.TacMutualCofix (a,b)
  | Tacexpr.TacAssert (a,b,c,d,e)        -> ITac.TacAssert (a,b,c,d,e)
  | Tacexpr.TacGeneralize a              -> ITac.TacGeneralize a
  | Tacexpr.TacLetTac (a,b,c,d,e,f)      -> ITac.TacLetTac (a,b,c,d,e,f)
  | Tacexpr.TacInductionDestruct (a,b,c) -> ITac.TacInductionDestruct (a,b,c)
  | Tacexpr.TacReduce (a,b)              -> ITac.TacReduce (a,b)
  | Tacexpr.TacChange (a,b,c)            -> ITac.TacChange (a,b,c)
  | Tacexpr.TacRewrite (a,b,c,d)         -> ITac.TacRewrite (a,b,c,d)
  | Tacexpr.TacInversion (a,b)           -> ITac.TacInversion (a,b)
and _gen_tactic_arg_put (t : 'a Tacexpr.gen_tactic_arg) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_arg = match t with
  | Tacexpr.TacGeneric a      -> ITac.TacGeneric a
  | Tacexpr.ConstrMayEval a   -> ITac.ConstrMayEval a
  | Tacexpr.Reference a       -> ITac.Reference a
  | Tacexpr.TacCall (a,(b,c)) -> ITac.TacCall (a,(b, List.map _gen_tactic_arg_put c))
  | Tacexpr.TacFreshId a      -> ITac.TacFreshId a
  | Tacexpr.Tacexp a          -> ITac.Tacexp a
  | Tacexpr.TacPretype a      -> ITac.TacPretype a
  | Tacexpr.TacNumgoals       -> ITac.TacNumgoals
and _gen_tactic_expr_put (t : 'a Tacexpr.gen_tactic_expr) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_expr =
  let u  x = _gen_tactic_expr_put x in
  let uu x = List.map u x           in
  let ua x = Array.map u x          in
  match t with
  | Tacexpr.TacAtom (a,b)            -> ITac.TacAtom (a,_gen_atom_tactic_expr_put b)
  | Tacexpr.TacThen (a,b)            -> ITac.TacThen (u a, u b)
  | Tacexpr.TacDispatch a            -> ITac.TacDispatch (uu a)
  | Tacexpr.TacExtendTac (a,b,c)     -> ITac.TacExtendTac (ua a, u b, ua c)
  | Tacexpr.TacThens (a,b)           -> ITac.TacThens (u a, uu b)
  | Tacexpr.TacThens3parts (a,b,c,d) -> ITac.TacThens3parts (u a, ua b, u c, ua d)
  | Tacexpr.TacFirst a               -> ITac.TacFirst (uu a)
  | Tacexpr.TacComplete a            -> ITac.TacComplete (u a)
  | Tacexpr.TacSolve a               -> ITac.TacSolve (uu a)
  | Tacexpr.TacTry a                 -> ITac.TacTry (u a)
  | Tacexpr.TacOr (a,b)              -> ITac.TacOr (u a, u b)
  | Tacexpr.TacOnce a                -> ITac.TacOnce (u a)
  | Tacexpr.TacExactlyOnce a         -> ITac.TacExactlyOnce (u a)
  | Tacexpr.TacIfThenCatch (a,b,c)   -> ITac.TacIfThenCatch (u a,u b,u c)
  | Tacexpr.TacOrelse (a,b)          -> ITac.TacOrelse (u a,u b)
  | Tacexpr.TacDo (a,b)              -> ITac.TacDo (a,u b)
  | Tacexpr.TacTimeout (a,b)         -> ITac.TacTimeout (a,u b)
  | Tacexpr.TacTime (a,b)            -> ITac.TacTime (a,u b)
  | Tacexpr.TacRepeat a              -> ITac.TacRepeat (u a)
  | Tacexpr.TacProgress a            -> ITac.TacProgress (u a)
  | Tacexpr.TacShowHyps a            -> ITac.TacShowHyps (u a)
  | Tacexpr.TacAbstract (a,b)        -> ITac.TacAbstract (u a,b)
  | Tacexpr.TacId a                  -> ITac.TacId a
  | Tacexpr.TacFail (a,b,c)          -> ITac.TacFail (a,b,c)
  | Tacexpr.TacInfo a                -> ITac.TacInfo (u a)
  (* | TacLetIn of rec_flag * *)
  (*     (Names.Id.t located * 'a gen_tactic_arg) list * *)
  (*     'a gen_tactic_expr *)
  | Tacexpr.TacLetIn (a, l, t) ->
    let _pt = List.map (fun (a,t) -> (a,_gen_tactic_arg_put t)) in
    ITac.TacLetIn (a, _pt l, _gen_tactic_expr_put t)
  (* | TacMatch of lazy_flag * *)
  (*     'a gen_tactic_expr * *)
  (*     ('p,'a gen_tactic_expr) match_rule list *)
  (* type ('a,'t) match_rule = *)
  (* | Pat of 'a match_context_hyps list * 'a match_pattern * 't *)
  (* | All of 't *)
  | Tacexpr.TacMatch (a, e, mr)      ->
    let _pmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_put t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_put e)
      ) in
    ITac.TacMatch(a, _gen_tactic_expr_put e, _pmr mr)
  | Tacexpr.TacMatchGoal (e, d, t)  ->
    let _pmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_put t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_put e)
      ) in
    ITac.TacMatchGoal(e, d, _pmr t)
  | Tacexpr.TacFun a                 -> ITac.TacFun (_gen_tactic_fun_ast_put a)
  | Tacexpr.TacArg (l,a)             -> ITac.TacArg (l, _gen_tactic_arg_put a)
  | Tacexpr.TacSelect(gs,te)         -> ITac.TacSelect(gs, _gen_tactic_expr_put te)
  | Tacexpr.TacML (a,(b,c))          -> ITac.TacML (a,(b, List.map _gen_tactic_arg_put c))
  | Tacexpr.TacAlias (a,(b,c))       -> ITac.TacAlias (a,(b, List.map _gen_tactic_arg_put c))
and _gen_tactic_fun_ast_put (t : 'a Tacexpr.gen_tactic_fun_ast) :
  ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_fun_ast =
  match t with
  | (a,b) -> (a, _gen_tactic_expr_put b)

let rec _gen_atom_tactic_expr_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_atomic_tactic_expr) :
  'a Tacexpr.gen_atomic_tactic_expr = match t with
  | ITac.TacIntroPattern(a,b)         -> Tacexpr.TacIntroPattern(a,b)
  | ITac.TacApply (a,b,c,d)           -> Tacexpr.TacApply (a,b,c,d)
  | ITac.TacElim (a,b,c)              -> Tacexpr.TacElim (a,b,c)
  | ITac.TacCase (a,b)                -> Tacexpr.TacCase (a,b)
  | ITac.TacMutualFix (a,b,c)         -> Tacexpr.TacMutualFix (a,b,c)
  | ITac.TacMutualCofix (a,b)         -> Tacexpr.TacMutualCofix (a,b)
  | ITac.TacAssert (a,b,c,d,e)        -> Tacexpr.TacAssert (a,b,c,d,e)
  | ITac.TacGeneralize a              -> Tacexpr.TacGeneralize a
  | ITac.TacLetTac (a,b,c,d,e,f)      -> Tacexpr.TacLetTac (a,b,c,d,e,f)
  | ITac.TacInductionDestruct (a,b,c) -> Tacexpr.TacInductionDestruct (a,b,c)
  | ITac.TacReduce (a,b)              -> Tacexpr.TacReduce (a,b)
  | ITac.TacChange (a,b,c)            -> Tacexpr.TacChange (a,b,c)
  | ITac.TacRewrite (a,b,c,d)         -> Tacexpr.TacRewrite (a,b,c,d)
  | ITac.TacInversion (a,b)           -> Tacexpr.TacInversion (a,b)
and _gen_tactic_arg_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_arg) :
  'a Tacexpr.gen_tactic_arg = match t with
  | ITac.TacGeneric a      -> Tacexpr.TacGeneric a
  | ITac.ConstrMayEval a   -> Tacexpr.ConstrMayEval a
  | ITac.Reference a       -> Tacexpr.Reference a
  | ITac.TacCall (a,(b,c)) -> Tacexpr.TacCall (a,(b, List.map _gen_tactic_arg_get c))
  | ITac.TacFreshId a      -> Tacexpr.TacFreshId a
  | ITac.Tacexp a          -> Tacexpr.Tacexp a
  | ITac.TacPretype a      -> Tacexpr.TacPretype a
  | ITac.TacNumgoals       -> Tacexpr.TacNumgoals
and _gen_tactic_expr_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_expr) :
  'a Tacexpr.gen_tactic_expr =
  let u  x = _gen_tactic_expr_get x in
  let uu x = List.map u x           in
  let ua x = Array.map u x          in
  match t with
  | ITac.TacAtom (a,b)            -> Tacexpr.TacAtom (a,_gen_atom_tactic_expr_get b)
  | ITac.TacThen (a,b)            -> Tacexpr.TacThen (u a, u b)
  | ITac.TacDispatch a            -> Tacexpr.TacDispatch (uu a)
  | ITac.TacExtendTac (a,b,c)     -> Tacexpr.TacExtendTac (ua a, u b, ua c)
  | ITac.TacThens (a,b)           -> Tacexpr.TacThens (u a, uu b)
  | ITac.TacThens3parts (a,b,c,d) -> Tacexpr.TacThens3parts (u a, ua b, u c, ua d)
  | ITac.TacFirst a               -> Tacexpr.TacFirst (uu a)
  | ITac.TacComplete a            -> Tacexpr.TacComplete (u a)
  | ITac.TacSolve a               -> Tacexpr.TacSolve (uu a)
  | ITac.TacTry a                 -> Tacexpr.TacTry (u a)
  | ITac.TacOr (a,b)              -> Tacexpr.TacOr (u a, u b)
  | ITac.TacOnce a                -> Tacexpr.TacOnce (u a)
  | ITac.TacExactlyOnce a         -> Tacexpr.TacExactlyOnce (u a)
  | ITac.TacIfThenCatch (a,b,c)   -> Tacexpr.TacIfThenCatch (u a,u b,u c)
  | ITac.TacOrelse (a,b)          -> Tacexpr.TacOrelse (u a,u b)
  | ITac.TacDo (a,b)              -> Tacexpr.TacDo (a,u b)
  | ITac.TacTimeout (a,b)         -> Tacexpr.TacTimeout (a,u b)
  | ITac.TacTime (a,b)            -> Tacexpr.TacTime (a,u b)
  | ITac.TacRepeat a              -> Tacexpr.TacRepeat (u a)
  | ITac.TacProgress a            -> Tacexpr.TacProgress (u a)
  | ITac.TacShowHyps a            -> Tacexpr.TacShowHyps (u a)
  | ITac.TacAbstract (a,b)        -> Tacexpr.TacAbstract (u a,b)
  | ITac.TacId a                  -> Tacexpr.TacId a
  | ITac.TacFail (a,b,c)          -> Tacexpr.TacFail (a,b,c)
  | ITac.TacInfo a                -> Tacexpr.TacInfo (u a)
  | ITac.TacLetIn (a, l, t)       ->
    let _pt = List.map (fun (a,t) -> (a,_gen_tactic_arg_get t)) in
    Tacexpr.TacLetIn (a, _pt l, _gen_tactic_expr_get t)
  | ITac.TacMatch (a,e,mr)          ->
    let _gmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_get t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_get e)
      ) in
    Tacexpr.TacMatch(a, _gen_tactic_expr_get e, _gmr mr)
  | ITac.TacMatchGoal (a,d,t)     ->
    let _gmr = List.map (function
        | Tacexpr.Pat (a,b,t) -> Tacexpr.Pat (a,b,_gen_tactic_expr_get t)
        | Tacexpr.All e       -> Tacexpr.All (_gen_tactic_expr_get e)
      ) in
    Tacexpr.TacMatchGoal(a,d, _gmr t)
  | ITac.TacFun a                 -> Tacexpr.TacFun (_gen_tactic_fun_ast_get a)
  | ITac.TacArg (l,a)             -> Tacexpr.TacArg (l, _gen_tactic_arg_get a)
  | ITac.TacSelect(gs,te)         -> Tacexpr.TacSelect(gs, _gen_tactic_expr_get te)
  | ITac.TacML (a,(b,c))          -> Tacexpr.TacML (a,(b,List.map _gen_tactic_arg_get c))
  | ITac.TacAlias (a,(b,c))       -> Tacexpr.TacAlias (a,(b,List.map _gen_tactic_arg_get c))
and _gen_tactic_fun_ast_get (t : ('t, 'dtrm, 'p, 'c, 'r, 'n, 'tacexpr, 'l) ITac.gen_tactic_fun_ast) :
  'a Tacexpr.gen_tactic_fun_ast =
  match t with
  | (a,b) -> (a, _gen_tactic_expr_get b)

type 'd gen_atomic_tactic_expr = 'd Tacexpr.gen_atomic_tactic_expr

let sexp_of_gen_atomic_tactic_expr
  t d p c r n te l (tac : 'a Tacexpr.gen_atomic_tactic_expr) : Sexp.t =
  ITac.sexp_of_gen_atomic_tactic_expr t d p c r n te l (_gen_atom_tactic_expr_put tac)

let sexp_of_gen_tactic_expr
  t d p c r n te l (tac : 'a Tacexpr.gen_tactic_expr) : Sexp.t =
  ITac.sexp_of_gen_tactic_expr t d p c r n te l (_gen_tactic_expr_put tac)

let sexp_of_gen_tactic_arg
  t d p c r n te l (tac : 'a Tacexpr.gen_tactic_arg) : Sexp.t =
  ITac.sexp_of_gen_tactic_arg t d p c r n te l (_gen_tactic_arg_put tac)

let sexp_of_gen_fun_ast
  t d p c r n te l (tac : 'a Tacexpr.gen_tactic_fun_ast) : Sexp.t =
  ITac.sexp_of_gen_tactic_fun_ast t d p c r n te l (_gen_tactic_fun_ast_put tac)

let gen_atomic_tactic_expr_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_atomic_tactic_expr =
  _gen_atom_tactic_expr_get (ITac.gen_atomic_tactic_expr_of_sexp t d p c r n te l tac)

let gen_tactic_expr_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_tactic_expr =
  _gen_tactic_expr_get (ITac.gen_tactic_expr_of_sexp t d p c r n te l tac)

let gen_tactic_arg_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_tactic_arg =
  _gen_tactic_arg_get (ITac.gen_tactic_arg_of_sexp t d p c r n te l tac)

let gen_fun_ast_of_sexp (tac : Sexp.t)
  t d p c r n te l : 'a Tacexpr.gen_tactic_fun_ast =
  _gen_tactic_fun_ast_get (ITac.gen_tactic_fun_ast_of_sexp t d p c r n te l tac)

(************************************************************************)
(* Main tactics types, we follow tacexpr and provide glob,raw, and      *)
(* atomic                                                               *)
(************************************************************************)

(* Glob *)
type glob_constr_and_expr =
  [%import: Tacexpr.glob_constr_and_expr]
  [@@deriving sexp]

type binding_bound_vars =
  [%import: Tacexpr.binding_bound_vars]
  [@@deriving sexp]

type glob_constr_pattern_and_expr =
  [%import: Tacexpr.glob_constr_pattern_and_expr]
  [@@deriving sexp]

type glob_tactic_expr = Tacexpr.glob_tactic_expr
type glob_atomic_tactic_expr = Tacexpr.glob_atomic_tactic_expr

let rec glob_tactic_expr_of_sexp tac =
  gen_tactic_expr_of_sexp
    tac
    glob_constr_and_expr_of_sexp
    glob_constr_and_expr_of_sexp
    glob_constr_pattern_and_expr_of_sexp
    (Locus.or_var_of_sexp (Stdarg.and_short_name_of_sexp Names.evaluable_global_reference_of_sexp))
    (Locus.or_var_of_sexp (Loc.located_of_sexp ltac_constant_of_sexp))
    Names.lident_of_sexp
    glob_tactic_expr_of_sexp
    Genarg.glevel_of_sexp
and glob_atomic_tactic_expr_of_sexp tac =
  gen_atomic_tactic_expr_of_sexp
    tac
    glob_constr_and_expr_of_sexp
    glob_constr_and_expr_of_sexp
    glob_constr_pattern_and_expr_of_sexp
    (Locus.or_var_of_sexp (Stdarg.and_short_name_of_sexp Names.evaluable_global_reference_of_sexp))
    (Locus.or_var_of_sexp (Loc.located_of_sexp ltac_constant_of_sexp))
    Names.lident_of_sexp
    glob_tactic_expr_of_sexp
    Genarg.glevel_of_sexp

let rec sexp_of_glob_tactic_expr (tac : glob_tactic_expr) =
  sexp_of_gen_tactic_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_pattern_and_expr
    (Locus.sexp_of_or_var (Stdarg.sexp_of_and_short_name Names.sexp_of_evaluable_global_reference))
    (Locus.sexp_of_or_var (Loc.sexp_of_located sexp_of_ltac_constant))
    Names.sexp_of_lident
    sexp_of_glob_tactic_expr
    Genarg.sexp_of_glevel
    tac
and sexp_of_glob_atomic_tactic_expr (tac : glob_atomic_tactic_expr) =
  sexp_of_gen_atomic_tactic_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_and_expr
    sexp_of_glob_constr_pattern_and_expr
    (Locus.sexp_of_or_var (Stdarg.sexp_of_and_short_name Names.sexp_of_evaluable_global_reference))
    (Locus.sexp_of_or_var (Loc.sexp_of_located sexp_of_ltac_constant))
    Names.sexp_of_lident
    sexp_of_glob_tactic_expr
    Genarg.sexp_of_glevel
    tac

(* Raw *)
type raw_tactic_expr = Tacexpr.raw_tactic_expr
type raw_atomic_tactic_expr = Tacexpr.raw_atomic_tactic_expr

let rec raw_tactic_expr_of_sexp tac =
  gen_tactic_expr_of_sexp
    tac
    Constrexpr.constr_expr_of_sexp
    Constrexpr.constr_expr_of_sexp
    Constrexpr.constr_pattern_expr_of_sexp
    (Constrexpr.or_by_notation_of_sexp Libnames.qualid_of_sexp)
    Libnames.qualid_of_sexp
    Names.lident_of_sexp
    raw_tactic_expr_of_sexp
    Genarg.rlevel_of_sexp
and raw_atomic_tactic_expr_of_sexp tac =
  gen_atomic_tactic_expr_of_sexp
    tac
    Constrexpr.constr_expr_of_sexp
    Constrexpr.constr_expr_of_sexp
    Constrexpr.constr_pattern_expr_of_sexp
    (Constrexpr.or_by_notation_of_sexp Libnames.qualid_of_sexp)
    Libnames.qualid_of_sexp
    Names.lident_of_sexp
    raw_tactic_expr_of_sexp
    Genarg.rlevel_of_sexp

let rec sexp_of_raw_tactic_expr (tac : raw_tactic_expr) =
  sexp_of_gen_tactic_expr
    Constrexpr.sexp_of_constr_expr
    Constrexpr.sexp_of_constr_expr
    Constrexpr.sexp_of_constr_pattern_expr
    (Constrexpr.sexp_of_or_by_notation Libnames.sexp_of_qualid)
    Libnames.sexp_of_qualid
    Names.sexp_of_lident
    sexp_of_raw_tactic_expr
    Genarg.sexp_of_rlevel
    tac
and sexp_of_raw_atomic_tactic_expr tac =
  sexp_of_gen_atomic_tactic_expr
    Constrexpr.sexp_of_constr_expr
    Constrexpr.sexp_of_constr_expr
    Constrexpr.sexp_of_constr_pattern_expr
    (Constrexpr.sexp_of_or_by_notation Libnames.sexp_of_qualid)
    Libnames.sexp_of_qualid
    Names.sexp_of_lident
    sexp_of_raw_tactic_expr
    Genarg.sexp_of_rlevel
    tac

(* Atomic *)
type atomic_tactic_expr = Tacexpr.atomic_tactic_expr

let atomic_tactic_expr_of_sexp tac =
  gen_atomic_tactic_expr_of_sexp tac
    EConstr.t_of_sexp
    glob_constr_and_expr_of_sexp
    Pattern.constr_pattern_of_sexp
    Names.evaluable_global_reference_of_sexp
    (Loc.located_of_sexp ltac_constant_of_sexp)
    Names.Id.t_of_sexp
    unit_of_sexp
    Genarg.tlevel_of_sexp

let sexp_of_atomic_tactic_expr tac =
  sexp_of_gen_atomic_tactic_expr
    EConstr.sexp_of_t
    sexp_of_glob_constr_and_expr
    Pattern.sexp_of_constr_pattern
    Names.sexp_of_evaluable_global_reference
    (Loc.sexp_of_located sexp_of_ltac_constant)
    Names.Id.sexp_of_t
    sexp_of_unit
    Genarg.sexp_of_tlevel
    tac

(* Helpers for raw_red_expr *)
type r_trm =
  [%import: Tacexpr.r_trm]
  [@@deriving sexp]

type r_cst =
  [%import: Tacexpr.r_cst]
  [@@deriving sexp]

type r_pat =
  [%import: Tacexpr.r_pat]
  [@@deriving sexp]

type raw_red_expr =
  [%import: Tacexpr.raw_red_expr]
  [@@deriving sexp]

type tacdef_body =
  [%import: Tacexpr.tacdef_body]
  [@@deriving sexp]

(* Unsupported serializers *)
type 'a delayed_open =
  [%import: 'a Tacexpr.delayed_open]

let sexp_of_delayed_open _ =
  Serlib_base.sexp_of_opaque ~typ:"delayed_open"
let delayed_open_of_sexp _ =
  Serlib_base.opaque_of_sexp ~typ:"delayed_open"

type delayed_open_constr_with_bindings =
  [%import: Tacexpr.delayed_open_constr_with_bindings]
  [@@deriving sexp]

type delayed_open_constr =
  [%import: Tacexpr.delayed_open_constr]
  [@@deriving sexp]

type intro_pattern =
  [%import: Tacexpr.intro_pattern]
  [@@deriving sexp]

