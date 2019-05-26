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
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module Ssrmatching = Ser_ssrmatching
open Ssrmatching

module Ltac_plugin = struct
  module Tacexpr = Ser_tacexpr
end

module Ssrast = Ser_ssrast

module Ssreflect_plugin = struct
  module Ssrast = Ser_ssrast
  module Ssrequality = Ser_ssrequality
  module Ssrparser = Ssreflect_plugin.Ssrparser
end

open! Ssrast

type t_movearg = (cpattern ssragens) ssrmovearg
[@@deriving sexp]

let ser_wit_ssrmovearg  =
  Ser_genarg.mk_uniform sexp_of_t_movearg t_movearg_of_sexp

let ser_wit_ssrapplyarg =
  Ser_genarg.mk_uniform sexp_of_ssrapplyarg ssrapplyarg_of_sexp

let ser_wit_clauses =
  Ser_genarg.mk_uniform sexp_of_clauses clauses_of_sexp

type t_rwarg = Ssreflect_plugin.Ssrequality.ssrrwarg list [@@deriving sexp]

let ser_wit_ssrrwargs =
  Ser_genarg.mk_uniform sexp_of_t_rwarg t_rwarg_of_sexp

type t_h1 = Ltac_plugin.Tacexpr.raw_tactic_expr fwdbinders
[@@deriving sexp]

type t_h2 = Ltac_plugin.Tacexpr.glob_tactic_expr fwdbinders
[@@deriving sexp]

  module Tacinterp = struct
    module Value = struct
      type t = [%import: Ltac_plugin.Tacinterp.Value.t]
      let t_of_sexp = Ser_geninterp.Val.t_of_sexp
      let sexp_of_t = Ser_geninterp.Val.sexp_of_t
    end
  end

type t_h3 = Tacinterp.Value.t fwdbinders
[@@deriving sexp]

let ser_wit_ssrhavefwdwbinders =
  Ser_genarg.{
    raw_ser = sexp_of_t_h1;
    raw_des = t_h1_of_sexp;

    glb_ser = sexp_of_t_h2;
    glb_des = t_h2_of_sexp;

    top_ser = sexp_of_t_h3;
    top_des = t_h3_of_sexp;
  }

let register () =
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrcasearg  ser_wit_ssrmovearg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrapplyarg ser_wit_ssrapplyarg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrmovearg  ser_wit_ssrmovearg;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrclauses  ser_wit_clauses;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrrwargs   ser_wit_ssrrwargs;
  Ser_genarg.register_genser Ssreflect_plugin.Ssrparser.wit_ssrhavefwdwbinders ser_wit_ssrhavefwdwbinders;
  ()

let _ = register ()
