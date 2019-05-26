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

(************************************************************************)
(* Based on Sexplib, (c) Jane Street, released under Apache License 2.0 *)
(* Custom sexp printer                                                  *)
(*                                                                      *)
(* Current sexplib escaping is not the most convenient for some clients *)
(* so we provide a different, experimental one                          *)
(************************************************************************)

open Format
open Sexplib
open Sexp

let must_escape str =
  let len = String.length str in
  len = 0 ||
    let rec loop ix =
      match str.[ix] with
      | '"' | '(' | ')' | '[' | ']' | ';' | '\\' | '\''-> true
      (* Avoid unquoted comma at the beggining of the string *)
      | ',' -> ix = 0 || loop (ix - 1)
      | '|' -> ix > 0 && let next = ix - 1 in str.[next] = '#' || loop next
      | '#' -> ix > 0 && let next = ix - 1 in str.[next] = '|' || loop next
      | '\000' .. '\032' -> true
      | '\248' .. '\255' -> true
      | _ -> ix > 0 && loop (ix - 1)
    in
    loop (len - 1)

(* XXX: Be faithful to UTF-8 *)
let st_escaped (s : string) =
  let sget = String.unsafe_get in
  let open Bytes in
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n +
      (match sget s i with
       | '\"' | '\\' | '\n' | '\t' | '\r' | '\b' -> 2
       | ' ' .. '~' -> 1
       (* UTF-8 are valid between \033 -- \247 *)
       | '\000' .. '\032' -> 4
       | '\248' .. '\255' -> 4
       | _                -> 1)
  done;
  if !n = String.length s then Bytes.of_string s else begin
    let s' = create !n in
    n := 0;
    for i = 0 to String.length s - 1 do
      begin match sget s i with
      | ('\"' | '\\') as c ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n c
      | '\n' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'n'
      | '\t' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 't'
      | '\r' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'r'
      | '\b' ->
          unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'b'
      | (' ' .. '~') as c -> unsafe_set s' !n c
      (* Valid UTF-8 are valid between \033 -- \247 *)
      | '\000' .. '\032'
      | '\248' .. '\255' as c ->
          let a = Char.code c in
          unsafe_set s' !n '\\';
          incr n;
          unsafe_set s' !n (Char.chr (48 + a / 100));
          incr n;
          unsafe_set s' !n (Char.chr (48 + (a / 10) mod 10));
          incr n;
          unsafe_set s' !n (Char.chr (48 + a mod 10));
      | c -> unsafe_set s' !n c
      end;
      incr n
    done;
    s'
  end

let esc_str (str : string) =
  let open Bytes in
  let estr = st_escaped str in
  let elen = length estr in
  let res  = create (elen + 2) in
  blit estr 0 res 1 elen;
  set res 0 '"';
  set res (elen + 1) '"';
  to_string res

let sertop_maybe_esc_str str =
  if must_escape str then esc_str str else str

let rec pp_sertop_internal may_need_space ppf = function
  | Atom str ->
      let str' = sertop_maybe_esc_str str in
      let new_may_need_space = str' == str in
      if may_need_space && new_may_need_space then pp_print_string ppf " ";
      pp_print_string ppf str';
      new_may_need_space
  | List (h :: t) ->
      pp_print_string ppf "(";
      let may_need_space = pp_sertop_internal false ppf h in
      pp_sertop_rest may_need_space ppf t;
      false
  | List [] -> pp_print_string ppf "()"; false

and pp_sertop_rest may_need_space ppf = function
  | h :: t ->
      let may_need_space = pp_sertop_internal may_need_space ppf h in
      pp_sertop_rest may_need_space ppf t
  | [] -> pp_print_string ppf ")"

let pp_sertop ppf sexp = ignore (pp_sertop_internal false ppf sexp)

(* XXX: This is terrible and doesn't work yet *)
let rec coq_pp_opt (d : Pp.t) = let open Pp in
  let rec flatten_glue l = match l with
    | []  -> []
    | (Ppcmd_glue g :: l) -> flatten_glue (List.map repr g @ flatten_glue l)
    | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> flatten_glue (Ppcmd_string (s1 ^ s2) :: flatten_glue l)
    | (x :: l) -> x :: flatten_glue l
  in
  (* let rec flatten_glue l = match l with *)
  (*   | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> Ppcmd_string (s1 ^ s2) :: flatten_glue l *)
  unrepr (match repr d with
      | Ppcmd_glue []   -> Ppcmd_empty
      | Ppcmd_glue [x]  -> repr (coq_pp_opt x)
      | Ppcmd_glue l    -> Ppcmd_glue List.(map coq_pp_opt (map unrepr (flatten_glue (map repr l))))
      | Ppcmd_box(bt,d) -> Ppcmd_box(bt, coq_pp_opt d)
      | Ppcmd_tag(t, d) -> Ppcmd_tag(t,  coq_pp_opt d)
      | d -> d
    )

(* Adjust positions from byte to UTF-8 chars *)
(* XXX: Move to serapi/ *)
(* We only do adjustement for messages for now. *)
module F = Feedback

let feedback_content_pos_filter txt (fbc : F.feedback_content) : F.feedback_content =
  let adjust _txt loc = loc in
  match (fbc : F.feedback_content) with
  | F.Message (lvl,loc,msg) -> F.Message (lvl, adjust txt loc, msg)
  | _                       -> fbc

let feedback_pos_filter text (fb : F.feedback) : F.feedback =
  { fb with F.contents = feedback_content_pos_filter text fb.F.contents; }


(* Optimizes and filters feedback *)
type fb_filter_opts = {
  pp_opt : bool;
}

let default_fb_filter_opts = {
  pp_opt = true;
}

let feedback_opt_filter ?(opts=default_fb_filter_opts) = let open Feedback in function
    | { F.contents = Message (lvl, loc, msg); _ } as fb ->
      Some (if opts.pp_opt
            then { fb with contents = Message(lvl, loc, coq_pp_opt msg) }
            else fb)
    | { F.contents = FileDependency _ ; _ } -> None
    | fb -> Some fb
