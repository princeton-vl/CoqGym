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

val pp_sertop : Format.formatter -> Sexp.t -> unit

val coq_pp_opt : Pp.t -> Pp.t

val feedback_pos_filter : string -> Feedback.feedback -> Feedback.feedback

(* Optimizer/filter for feedback *)
type fb_filter_opts = {
  pp_opt : bool;
}

val default_fb_filter_opts : fb_filter_opts

val feedback_opt_filter : ?opts:fb_filter_opts -> Feedback.feedback -> Feedback.feedback option
