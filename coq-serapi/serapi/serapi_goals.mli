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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* We ship our own type due to Context lack of support for anything
   other than Constr.t *)
type 'a hyp = (Names.Id.t list * 'a option * 'a)
type 'a reified_goal = { name: string; ty: 'a; hyp: 'a hyp list }

(* Ready to make into a GADT *)
val get_goals  : doc:Stm.doc -> Stateid.t -> Constr.t               reified_goal Proof.pre_goals option
val get_egoals : doc:Stm.doc -> Stateid.t -> Constrexpr.constr_expr reified_goal Proof.pre_goals option
