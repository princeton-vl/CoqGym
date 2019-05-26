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
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type ax_ctx = (Names.Label.t * Constr.rel_context * Constr.t) list

type t =
  { predicative : Declarations.set_predicativity
  ; type_in_type : bool
  ; vars   : (Names.Id.t * Constr.t) list
  ; axioms : (Printer.axiom * Constr.t * ax_ctx) list
  ; opaque : (Names.Constant.t * Constr.t) list
  ; trans  : (Names.Constant.t * Constr.t) list
  }

let build env ctxmap =
  let open Printer in
  let fold t typ accu =
    let (v, a, o, tr) = accu in
    match t with
    | Variable id ->
      ((id,typ) :: v, a, o, tr)
    | Axiom (axiom, l) ->
      (v, (axiom,typ,l) :: a, o, tr)
    | Opaque kn ->
      (v, a, (kn,typ) :: o, tr)
    | Transparent kn ->
      (v, a, o, (kn,typ) :: tr)
  in
  let (vars, axioms, opaque, trans) =
    ContextObjectMap.fold fold ctxmap ([], [], [], []) in
  { predicative = Environ.engagement env
  ; type_in_type = Environ.type_in_type env
  ; vars
  ; axioms
  ; opaque
  ; trans
  }

let print env sigma { predicative; type_in_type; vars; axioms; opaque; trans } =
  let pr_engament e =
    match e with
    | Declarations.ImpredicativeSet -> Pp.str "Set is Impredicative"
    | Declarations.PredicativeSet -> Pp.str "Set is Predicative"
  in
  let pr_var env sigma (id, typ) =
    Pp.(seq [Names.Id.print id; str " : "; Printer.pr_ltype_env env sigma typ ])
  in
  let pr_constant env sigma (cst, typ) =
    Pp.(seq [Names.Constant.print cst; str " : "; Printer.pr_ltype_env env sigma typ ])
  in
  let pr_axiom env sigma (ax, typ, lctx) =
    let pr_ax env sigma typ a =
      let open Printer in
      match a with
      | Constant kn ->
        Pp.(seq [Names.Constant.print kn; str " : "; Printer.pr_ltype_env env sigma typ])
      | Positive m ->
        Pp.(seq [Printer.pr_inductive env (m,0); str "is positive."])
      | Guarded kn ->
        Pp.(seq [Names.Constant.print kn; str "is positive."])
    in
    Pp.(seq [
        pr_ax env sigma typ ax
      ; prlist (fun (lbl, ctx, ty) ->
            str " used in " ++ Names.Label.print lbl ++
            str " to prove:" ++
            Printer.pr_ltype_env Environ.(push_rel_context ctx env) sigma ty) lctx
      ])
  in
  Pp.(v 0 (prlist_with_sep (fun _ -> cut ()) (fun x -> x) [
      if type_in_type then str "type_in_type is on" else mt ()
    ; pr_engament predicative
    ; hov 1 (prlist (pr_var env sigma) vars)
    ; hov 1 (prlist (pr_constant env sigma) opaque)
    ; hov 1 (prlist (pr_constant env sigma) trans)
    ; hov 1 (prlist (pr_axiom env sigma) axioms)
    ]))
