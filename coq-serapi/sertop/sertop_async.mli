(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API -- Async loop                                  *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

(** [sertop fb_handler] Initialize Coq and send serialized feedback to
    [fb_handler] *)
val sertop_init :
  fb_out:(Sexp.t -> unit) ->
  iload_path:Mltop.coq_path list ->
  require_libs:(string * string option * bool option) list ->
  debug:bool ->
  Stm.doc * Stateid.t

(** [sertop_callback out input] Execute command [input] and send
    serialized output to [out]. Takes an internal mutex. *)
val sertop_callback : (Sexp.t -> unit) -> Sexp.t -> unit
