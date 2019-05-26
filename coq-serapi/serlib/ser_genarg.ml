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

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

open Genarg

type rlevel =
  [%import: Genarg.rlevel]
  [@@deriving sexp]
type glevel =
  [%import: Genarg.glevel]
  [@@deriving sexp]
type tlevel =
  [%import: Genarg.tlevel]
  [@@deriving sexp]

open Sexp

let rec sexp_of_genarg_type : type a b c. (a, b, c) genarg_type -> t = fun gt ->
  match gt with
  | ExtraArg tag   -> List [Atom "ExtraArg"; Atom (ArgT.repr tag)]
  | ListArg rt     -> List [Atom "ListArg"; sexp_of_genarg_type rt]
  | OptArg  rt     -> List [Atom "OptArg";  sexp_of_genarg_type rt]
  | PairArg(t1,t2) -> List [Atom "PairArg"; sexp_of_genarg_type t1; sexp_of_genarg_type t2]

let sexp_of_abstract_argument_type : type lvl. ('o, lvl) abstract_argument_type -> t * t = fun  at ->
  match at with
  | Rawwit w -> Atom "raw", sexp_of_genarg_type w
  | Glbwit w -> Atom "glb", sexp_of_genarg_type w
  | Topwit w -> Atom "top", sexp_of_genarg_type w

let rec argument_type_of_sexp : t -> argument_type = fun sexp ->
  match sexp with
  | List [Atom "ExtraArg"; Atom tag] ->
    begin match ArgT.name tag with
      | None              -> raise (Failure "SEXP Exception in argument_type")
      | Some (ArgT.Any t) -> ArgumentType (ExtraArg t)
    end
  | List [Atom "ListArg"; s1] ->
    let (ArgumentType t) = argument_type_of_sexp s1 in
    ArgumentType (ListArg t)
  | List [Atom "OptArg";  s1] ->
    let (ArgumentType t) = argument_type_of_sexp s1 in
    ArgumentType (OptArg t)
  | List [Atom "PairArg"; s1; s2] ->
    let (ArgumentType t1) = argument_type_of_sexp s1 in
    let (ArgumentType t2) = argument_type_of_sexp s2 in
    ArgumentType (PairArg(t1,t2))
  | _ -> raise (Failure "SEXP Exception")

type ('raw, 'glb, 'top) gen_ser =
  { raw_ser : 'raw -> Sexp.t;
    raw_des : Sexp.t -> 'raw;

    glb_ser : 'glb -> Sexp.t;
    glb_des : Sexp.t -> 'glb;

    top_ser : 'top -> Sexp.t;
    top_des : Sexp.t -> 'top;
  }

let gen_ser_list :
  ('raw, 'glb, 'top) gen_ser ->
  ('raw list, 'glb list, 'top list) gen_ser = fun g ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_list g.raw_ser;
    raw_des = list_of_sexp g.raw_des;
    glb_ser = sexp_of_list g.glb_ser;
    glb_des = list_of_sexp g.glb_des;
    top_ser = sexp_of_list g.top_ser;
    top_des = list_of_sexp g.top_des;
  }

let gen_ser_opt :
  ('raw, 'glb, 'top) gen_ser ->
  ('raw option, 'glb option, 'top option) gen_ser = fun g ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_option g.raw_ser;
    raw_des = option_of_sexp g.raw_des;
    glb_ser = sexp_of_option g.glb_ser;
    glb_des = option_of_sexp g.glb_des;
    top_ser = sexp_of_option g.top_ser;
    top_des = option_of_sexp g.top_des;
  }

let gen_ser_pair :
  ('raw1, 'glb1, 'top1) gen_ser ->
  ('raw2, 'glb2, 'top2) gen_ser ->
  (('raw1 * 'raw2), ('glb1 * 'glb2), ('top1 * 'top2)) gen_ser = fun g1 g2 ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_pair g1.raw_ser g2.raw_ser;
    raw_des = pair_of_sexp g1.raw_des g2.raw_des;
    glb_ser = sexp_of_pair g1.glb_ser g2.glb_ser;
    glb_des = pair_of_sexp g1.glb_des g2.glb_des;
    top_ser = sexp_of_pair g1.top_ser g2.top_ser;
    top_des = pair_of_sexp g1.top_des g2.top_des;
  }

module SerObj = struct

  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) gen_ser

  let sexp_of_gen typ ga =
    let typ = typ ^ ": " ^ Sexp.to_string (sexp_of_genarg_type ga) in
    Serlib_base.sexp_of_opaque ~typ

  let name = "ser_arg"
  let default _ga =
    Some {
      (* raw_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "raw"; sexp_of_genarg_type ga])); *)
      raw_ser = sexp_of_gen "raw" _ga;
      raw_des = (Sexplib.Conv_error.no_matching_variant_found "raw_arg");

      (* glb_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "glb"; sexp_of_genarg_type ga])); *)
      glb_ser = sexp_of_gen "glb" _ga;
      glb_des = (Sexplib.Conv_error.no_matching_variant_found "glb_arg");

      (* top_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "top"; sexp_of_genarg_type ga])); *)
      top_ser = sexp_of_gen "top" _ga;
      top_des = (Sexplib.Conv_error.no_matching_variant_found "top_arg")
    }
end

module SerGen = Register(SerObj)
let register_genser ty obj = SerGen.register0 ty obj

let rec get_gen_ser_ty : type r g t. (r,g,t) Genarg.genarg_type -> (r,g,t) gen_ser =
  fun gt -> match gt with
  | Genarg.ExtraArg _      -> SerGen.obj gt
  | Genarg.ListArg  t      -> gen_ser_list (get_gen_ser_ty t)
  | Genarg.OptArg   t      -> gen_ser_opt  (get_gen_ser_ty t)
  | Genarg.PairArg(t1, t2) -> gen_ser_pair (get_gen_ser_ty t1) (get_gen_ser_ty t2)

let get_gen_ser : type lvl. ('o,lvl) abstract_argument_type -> ('o -> 't) = fun aty ->
  match aty with
  | Genarg.Rawwit ty -> (get_gen_ser_ty ty).raw_ser
  | Genarg.Glbwit ty -> (get_gen_ser_ty ty).glb_ser
  | Genarg.Topwit ty -> (get_gen_ser_ty ty).top_ser

let generic_des : type lvl. ('o,lvl) abstract_argument_type -> t -> lvl generic_argument = fun ty s ->
  match ty with
  | Genarg.Rawwit w -> GenArg(ty, (get_gen_ser_ty w).raw_des s)
  | Genarg.Glbwit w -> GenArg(ty, (get_gen_ser_ty w).glb_des s)
  | Genarg.Topwit w -> GenArg(ty, (get_gen_ser_ty w).top_des s)

(* We need to generalize this to use the proper printers for opt *)
let mk_sexparg (lvl, st) so =
  List [Atom "GenArg"; lvl; st; so]

(* XXX: There is still some duplication here in the traversal of g_ty, but
   we can live with that for now.  *)
let sexp_of_genarg_val : type a. a generic_argument -> Sexp.t =
  fun g -> match g with
  | GenArg (g_ty, g_val) ->
    mk_sexparg (sexp_of_abstract_argument_type g_ty) (get_gen_ser g_ty g_val)

let sexp_of_generic_argument : type a. (a -> t) -> a generic_argument -> t =
  fun _level_tag g ->
  sexp_of_genarg_val g

type rgen_argument = RG : 'lvl generic_argument -> rgen_argument
let gen_abstype_of_sexp : t -> rgen_argument = fun s ->
  match s with
  | List [Atom "GenArg"; Atom "raw"; sty; sobj] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    RG (generic_des (Rawwit ty) sobj)
  | List [Atom "GenArg"; Atom "glb"; sty; sobj] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    RG (generic_des (Glbwit ty) sobj)
  | List [Atom "GenArg"; Atom "top"; sty; sobj] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    RG (generic_des (Topwit ty) sobj)
  | _ -> raise (Failure "SEXP Exception in abstype")

let generic_argument_of_sexp _lvl sexp : 'a Genarg.generic_argument =
  let (RG ga) = gen_abstype_of_sexp sexp in
  Obj.magic ga

type 'a generic_argument = 'a Genarg.generic_argument

type glob_generic_argument =
  [%import: Genarg.glob_generic_argument]
  [@@deriving sexp]

type raw_generic_argument =
  [%import: Genarg.raw_generic_argument]
  [@@deriving sexp]

type typed_generic_argument =
  [%import: Genarg.typed_generic_argument]
  [@@deriving sexp]

let mk_uniform pin pout = {
    raw_ser = pin;
    glb_ser = pin;
    top_ser = pin;
    raw_des = pout;
    glb_des = pout;
    top_des = pout;
  }
