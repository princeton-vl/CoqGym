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

open Sexplib
open Sexplib.Conv

module SP = Serapi_protocol

(******************************************************************************)
(* Global Protocol Options                                                    *)
(******************************************************************************)

type ser_opts =
{ in_chan  : in_channel          (* Input/Output channels                      *)
; out_chan : out_channel
                                 (* Printers                                   *)
; printer  : Sertop_ser.ser_printer

; debug    : bool
; print0   : bool
; lheader  : bool                (* Print lenght header (deprecated)           *)

  (* Coq options *)
; no_init  : bool                (* Whether to create the initial document     *)

; loadpath : Mltop.coq_path list (* From -R and -Q options usually *)
; async    : Sertop_init.async_flags
}

(******************************************************************************)
(* Input/Output                                                               *)
(******************************************************************************)
(*                                                                            *)
(* Until this point, we've been independent of a particular format or         *)
(* or serialization, with all the operations defined at the symbolic level.   *)
(*                                                                            *)
(* It is now time to unfortunately abandon our fairy-tale and face the real,  *)
(* ugly world in these last 40 lines!                                         *)
(*                                                                            *)
(******************************************************************************)

let is_cmd_quit cmd = match cmd with
  | SP.Quit -> true
  | _    -> false

(* XXX: Improve by using manual tag parsing. *)
let read_cmd cmd_id in_channel pp_error =
  let rec read_loop () =
    try
      let cmd_sexp = Sexp.input_sexp in_channel in
      begin
        try Sertop_ser.tagged_cmd_of_sexp cmd_sexp
        with
        | End_of_file   -> "EOF", SP.Quit
        | _exn ->
          (string_of_int cmd_id), Sertop_ser.cmd_of_sexp cmd_sexp
      end
    with
    | End_of_file   -> "EOF", SP.Quit
    | exn           -> pp_error (sexp_of_exn exn);
                       read_loop ()
  in read_loop ()

let out_sexp opts =
  let open Format                                                               in

  let pp_sexp = Sertop_ser.select_printer opts.printer in

  let pp_term = if opts.print0 then fun fmt () -> fprintf fmt "%c" (Char.chr 0)
                               else fun fmt () -> fprintf fmt "@\n"             in
  if opts.lheader then
    fun fmt a ->
      fprintf str_formatter "@[%a@]%a%!" pp_sexp a pp_term ();
      let out = flush_str_formatter () in
      fprintf fmt "@[byte-length: %d@\n%s@]%!" (String.length out) out
  else
    fun fmt a -> fprintf fmt "@[%a@]%a%!" pp_sexp a pp_term ()

(** We could use Sexp.to_string too  *)
let out_answer opts =
  let pp_sexp = out_sexp opts in
  fun fmt a -> pp_sexp fmt (Sertop_ser.sexp_of_answer a)

let ser_loop ser_opts =

  let open List   in
  let open Format in

  (* XXX EG: I don't understand this well, why is this lock needed ??
     Review fork code in CoqworkmgrApi *)
  let pr_mutex     = Mutex.create ()                                   in
  let ser_lock f x = Mutex.lock   pr_mutex;
                     f x;
                     Mutex.unlock pr_mutex                             in
  let out_fmt      = formatter_of_out_channel ser_opts.out_chan        in
  let pp_answer    = ser_lock (out_answer ser_opts out_fmt)            in
  let pp_err       = ser_lock (out_sexp ser_opts out_fmt)              in
  let pp_ack cid   = pp_answer (SP.Answer (cid, SP.Ack))               in
  let pp_opt  fb   = Sertop_util.feedback_opt_filter fb                in
  let pp_feed fb   = Option.iter (fun fb -> pp_answer (SP.Feedback fb)) (pp_opt fb) in

  (* Init Coq *)
  let () = Sertop_init.(
      coq_init
        { fb_handler   = pp_feed
        ; ml_load      = None
        ; debug        = ser_opts.debug
        })
  in

  (* Follow the same approach than coqtop for now: allow Coq to be
   * interrupted by Ctrl-C. Not entirely safe or race free... but we
   * trust the IDEs to send the signal on coherent IO state.
   *)
  Sys.catch_break true;

  let require_libs = ["Coq.Init.Prelude", None, Some false] in
  let iload_path = ser_opts.loadpath in
  let stm_options = Sertop_init.process_stm_flags ser_opts.async in

  if not ser_opts.no_init then begin
    let sertop_dp = Names.(DirPath.make [Id.of_string "SerTop"]) in
    let ndoc = { Stm.doc_type = Stm.Interactive sertop_dp
               ; require_libs
               ; iload_path
               ; stm_options
               } in
    let _ = Stm.new_doc ndoc in
    ()
  end;

  (* Main loop *)
  let rec loop cmd_id =
    try
      let cmd_tag, cmd = read_cmd cmd_id ser_opts.in_chan pp_err          in
      pp_ack cmd_tag;
      iter pp_answer @@ map (fun a -> SP.Answer (cmd_tag, a)) (SP.exec_cmd cmd);
      if not (is_cmd_quit cmd) then loop (1+cmd_id)
    with Sys.Break -> loop (1+cmd_id)
  in loop 0
