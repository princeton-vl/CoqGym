(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* We perform a simple => sexp to text tranformation. We hook at the
 * constr_extern level to support notations, but this should be
 * replaced in the future by the new glob_constr printer.
 *)

open Format
open Sexplib

let rec pp_sexp_to_tex fmt s = let open Sexp in match s with
  | Atom s                -> fprintf fmt "%s" s
  | List []               -> ()
  | List [x]              -> pp_sexp_to_tex fmt x
  (* Specific Patterns *)
  | List (Atom "CNotation" :: _ :: l) ->
    pp_sexp_to_tex fmt @@ List (Atom "CoqNotation" :: l)
  | List (Atom "CPrim" :: _ :: l) ->
    pp_sexp_to_tex fmt @@ List (Atom "CoqPrim" :: l)
  | List (List (Atom "fname" :: _) :: _) -> ()
  (* | List (Atom "CNotation" :: _ :: u) -> pp_sexp_to_tex fmt @@ List (Atom "CNotation" :: u) *)
  (* General cases *)
  | List (Atom atm :: ll) -> fprintf fmt "@[\\%s%a@]" atm pp_list_items ll
  | List l                -> pp_list_items fmt l
and pp_list_items fmt = List.iter (fun i -> fprintf fmt "{@[%a@]}" pp_sexp_to_tex i)

