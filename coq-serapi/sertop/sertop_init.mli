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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type async_flags =
  { enable_async  : string option
  ; async_full    : bool
  ; deep_edits    : bool
  ; async_workers : int
  }
(** SerAPI flags for asynchronous processing *)

val process_stm_flags : async_flags -> Stm.AsyncOpts.stm_opt
(** [process_stm_flags flags] transforms SerAPI flags into Coq flags *)

type coq_opts =
  { fb_handler   : Feedback.feedback -> unit
  (** callback to handle async feedback *)

  ; ml_load      : (string -> unit) option
  (** callback to load cma/cmo files    *)

  ; debug        : bool
  (** Enable Coq Debug mode             *)
}

val coq_init : coq_opts -> unit
(** [coq_init opts] Initialize Coq. This doesn't create a Proof Document. *)
