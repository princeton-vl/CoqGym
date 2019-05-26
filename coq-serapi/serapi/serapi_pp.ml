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

open Format

(** This module includes all of sertop custom Format-based printers
    for Coq datatypes *)

type 'a pp = formatter -> 'a -> unit

(************************************************************************)
(* Print Helpers                                                        *)
(************************************************************************)

let pp_str fmt str = fprintf fmt "%s" str

let pp_opt pp fmt opt = match opt with
  | None   -> ()
  | Some x -> fprintf fmt "%a" pp x

let rec pp_list ?sep pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "@[%a@]" pp csx
  | csx :: csl -> fprintf fmt "@[%a@]%a@;%a" pp csx (pp_opt pp_str) sep (pp_list ?sep pp) csl

(************************************************************************)
(* Statid                                                               *)
(************************************************************************)
let pp_stateid fmt id = fprintf fmt "%d" (Stateid.to_int id)

(************************************************************************)
(* Feedback                                                             *)
(************************************************************************)
let pp_feedback_content fmt fb =
  let open Feedback in
  match fb with
  (* STM mandatory data (must be displayed) *)
  | Processed       -> fprintf fmt "Processed"
  | Incomplete      -> fprintf fmt "Incomplete"
  | Complete        -> fprintf fmt "Complete"

  (* STM optional data *)
  | ProcessingIn s       -> fprintf fmt "ProcessingIn: %s" s
  | InProgress d         -> fprintf fmt "InProgress: %d" d
  | WorkerStatus(w1, w2) -> fprintf fmt "WorkerStatus: %s, %s" w1 w2

  (* Generally useful metadata *)
  | AddedAxiom     -> fprintf fmt "AddedAxiom"

  | GlobRef (_loc, s1, s2, s3, s4) -> fprintf fmt "GlobRef: %s,%s,%s,%s" s1 s2 s3 s4
  | GlobDef (_loc, s1, s2, s3)     -> fprintf fmt "GlobDef: %s,%s,%s"    s1 s2 s3

  | FileDependency (os, s) -> fprintf fmt "FileDep: %a, %s" (pp_opt pp_str) os s
  | FileLoaded (s1, s2)    -> fprintf fmt "FileLoaded: %s, %s" s1 s2

  (* Extra metadata *)
  | Custom(_loc, msg, _xml) -> fprintf fmt "Custom: %s" msg

  (* Old generic messages *)
  | Message(_lvl, _loc, m) -> fprintf fmt "Msg: @[%a@]" Pp.pp_with m

let pp_feedback fmt (fb : Feedback.feedback) =
  let open Feedback in
  fprintf fmt "feedback for [%a]: @[%a@]" pp_stateid fb.span_id pp_feedback_content fb.Feedback.contents

(************************************************************************)
(* Xml                                                                  *)
(************************************************************************)
let pp_attr fmt (xtag, att) =
  fprintf fmt "%s = %s" xtag att

let rec pp_xml fmt (xml : Xml_datatype.xml) = match xml with
  | Xml_datatype.Element (tag, att, more) ->
    fprintf fmt "@[<%s @[%a@]>@,%a@,</%s>@]" tag (pp_list pp_attr) att (pp_list pp_xml) more tag
  | Xml_datatype.PCData str -> fprintf fmt "%s" str

