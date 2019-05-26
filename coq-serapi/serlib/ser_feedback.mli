(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type level = Feedback.level

val level_of_sexp : Sexp.t -> level
val sexp_of_level : level -> Sexp.t

type route_id = Feedback.route_id
val route_id_of_sexp : Sexp.t -> route_id
val sexp_of_route_id : route_id -> Sexp.t

type feedback_content = Feedback.feedback_content

val feedback_content_of_sexp : Sexp.t -> feedback_content
val sexp_of_feedback_content : feedback_content -> Sexp.t

type feedback = Feedback.feedback

val feedback_of_sexp : Sexp.t -> feedback
val sexp_of_feedback : feedback -> Sexp.t
