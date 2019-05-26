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

(* type goal_selector = Vernacexpr.goal_selector
 * val goal_selector_of_sexp : Sexp.t -> goal_selector
 * val sexp_of_goal_selector : goal_selector -> Sexp.t *)

open Sexplib.Conv

module Names       = Ser_names

type t =
  [%import: Goal_select.t]
  [@@deriving sexp]
