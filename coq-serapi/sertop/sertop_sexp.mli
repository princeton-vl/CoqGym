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

(************************************************************************)
(* Global Protocol Options                                              *)
(************************************************************************)

type ser_opts =
{ in_chan  : in_channel
; out_chan : out_channel         (** Input/Output channels                    *)

; printer  : Sertop_ser.ser_printer
                                 (** Printer type                             *)

; debug    : bool                (** Enable Coq debug mode                    *)
; print0   : bool                (** End every answer with [\0]               *)
; lheader  : bool                (** Print lenght header (deprecated)         *)

; no_init  : bool                (** Whether to create the initial document   *)

(* Coq options *)
; loadpath : Mltop.coq_path list (** From -R and -Q options usually           *)
; async    : Sertop_init.async_flags
                                 (** Async flags                              *)
}
(** Options for the sertop interactive toplevel                               *)

(******************************************************************************)
(* Input/Output -- Main Loop                                                  *)
(******************************************************************************)

val ser_loop : ser_opts -> unit
(** [ser_loop opts] main se(xp)r-protocol interactive loop *)
