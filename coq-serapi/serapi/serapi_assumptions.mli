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

val build : Environ.env -> Constr.t Printer.ContextObjectMap.t -> t
val print : Environ.env -> Evd.evar_map -> t -> Pp.t
