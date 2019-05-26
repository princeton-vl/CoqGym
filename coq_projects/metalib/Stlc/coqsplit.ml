(* coqsplit utility.

   Copyright 2016, Benjamin C. Pierce
   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:
   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
   THE SOFTWARE.
*)

let solutions = List.mem "-solutions" (Array.to_list Sys.argv)
let terse = List.mem "-terse" (Array.to_list Sys.argv)
let advanced = List.mem "-advanced" (Array.to_list Sys.argv)
let exerciselist = List.mem "-exerciselist" (Array.to_list Sys.argv)

(* (BCP: 12/15) This one was probably not a good idea :-( *)
let combined = List.mem "-combined" (Array.to_list Sys.argv)

(*
  coqsplit.ml
 * This file processes SF files in the base directory
 * and formats them for the subdirectories:
 *       full
 *       sol
 *       terse
 *       combined
 * A tag is a construct that picks out a fragment of input string
 * and transforms its contents. In the source file, tags are marked as:
 *	(** TAG: text *)
 * or
 *  (* TAG *)
 * text
 * (* /TAG *)
 *
 * An object of type tag_type is a 4-element list
 *		[start,end,transform,f]
 * where:
 *		start is a string denoting the beginning of the tag
 *		end is a string denoting the end of the tag
 *		transform is a function from strings to strings
 *			that acts on the content strictly between start and end
 *		f is a flag denoting Soak or NoSoak
 *
 * The soak flag controls the handling of newlines around the
 * matched region.
 *)
type soak = Soak | NoSoak

let sprintf = Printf.sprintf

let ex (ex_opt,rendered_opt) is_grading stars =
  let beg_code = sprintf "(* EX%d%s" stars ex_opt in
  let stars_str = if stars = 1 then "star" else "stars" in
  let beg_str name =
        if is_grading
        then sprintf "Exercise: %d stars%s%s." stars rendered_opt name
        else sprintf "(** **** Exercise: %d %s%s%s *)" stars stars_str rendered_opt name
        in
    [beg_code, "*)", beg_str, NoSoak ]


(* mk_exercises opt l
 * creates tags that format exercises corresponding to the options opt
 * with the star amounts given by the list l
 * (full, solutions)
 *)

let mk_exercises opt l =
  let first = List.fold_left (fun ls stars -> (ex opt false stars) @ ls) [] l in
  let end_code = "[] *)" in
  let end_str _ = "[] *)" in
  first @ [end_code, "", end_str, NoSoak]

(* gr_thm stars b
 * creats a tag that formats grading scripts for grading theorems, worth stars points
 * (grading)
 *)

let gr_thm b stars =
  let gr_str_beg = sprintf "(* GRADE_THEOREM %d: " stars in
  let gr_str_end = sprintf " *)\n" in
  let rendered_str s = if b then
        sprintf "Part: %d points \"Check proof assumptions\". Assump Test. Print Assumptions %s. /Assump. /Part.\n"
          stars s
        else ""
  in
          [gr_str_beg, gr_str_end, rendered_str, NoSoak]

(* mk_grade_thm l b
 * if b=true, creates tags that format grading scripts for grading theorems,
 * with the star amounts given by the list l
 * (grading)
 *)

let mk_grade_thm l b =
  List.flatten (List.map (gr_thm b) l)

let gr_manual b stars =
  let gr_str_beg = sprintf "(* GRADE_MANUAL %d: " stars in
  let gr_str_end = sprintf " *)\n" in
  let rendered_str s = if b then
        sprintf "Manual: %d points \"%s\".\n" stars s
        else ""
  in
  [gr_str_beg, gr_str_end, rendered_str, NoSoak]


(* mk_grade_manual l b
 * if b=true, creates tags that format grading scripts to denote that the
 * exercise must be manually graded.
 *)

let mk_grade_manual l b =
  List.flatten (List.map (gr_manual b) l)

let gr_ltac b stars =
  let gr_str_beg = sprintf "(* GRADE %d: " stars in
  let gr_str_end = sprintf " *)\n" in
  let rendered_str s = if b then s else "" in
  [gr_str_beg, gr_str_end, rendered_str, NoSoak]

(* mk_grade_ltac l b
 * if b=true, creates tags that format grading scripts written explicitly
 * in between:
 *		(* GRADE: script *)
 *)

let mk_grade_ltac l b =
  List.flatten (List.map (gr_ltac b) l)



let stars = [1;2;3;4;5]

(* mk_tag t b
 * constructs an object of type tag_type with no mutation of data.
 * If b, then NoSoak is set, otherwise Soak
 *)

let all_tags = ref []

let mk_tag t b =
  all_tags := t :: !all_tags;
  (* FOO: ... *)
  (if b then
     [ ("(* " ^ t ^ ":"), "", (fun _ -> "(*"), NoSoak]
   else
     [ ("(* " ^ t ^ ":"), "*)\n", (fun _ -> ""), Soak])
  @
  (** FOO: ... *)
  (if b then
     [ ("(** " ^ t ^ ":"), "", (fun _ -> "(**"), NoSoak]
   else
     [ ("(** " ^ t ^ ":"), "*)\n", (fun _ -> ""), Soak])
  @
  (* FOO *) (*...*) (* /FOO *)
  (if b then
     [ ("(* " ^ t ^ " *)"), "\n", (fun _ -> ""), NoSoak;
       ("(* /" ^ t ^ " *)"), "\n", (fun _ -> ""), NoSoak]
   else
     [ ("(* " ^ t ^ " *)"), ("(* /" ^ t ^ " *)\n"), (fun _ -> ""), Soak])

let mk_htmltag t tag rest =
  all_tags := t :: !all_tags;
  (* FOO: ... *)
  [ ("(* " ^ t ^ ":"), "*)\n",
       (fun s -> "(** #<" ^ tag ^ " " ^ rest ^ ">#"
                 ^ s ^ "\n#</" ^ tag ^ "># *)\n"), Soak]
  @
  (** FOO: ... *)
  [ ("(** " ^ t ^ ":"), "*)\n",
       (fun s -> "(** #<" ^ tag ^ " " ^ rest ^ ">#"
                 ^ s ^ "\n#</" ^ tag ^ "># *)\n"), Soak]
  @
  (* FOO *) (*...*) (* /FOO *)
  [ ("(* " ^ t ^ " *)"), ("(* /" ^ t ^ " *)\n"),
       (fun s -> "(** #<" ^ tag ^ " " ^ rest ^ "># *)"
                 ^ s ^ "\n(** #</" ^ tag ^ "># *)\n"), Soak]

let mk_soltag t ?(soltag = "(* SOLUTION: *)") ?(ns = NoSoak) s =
  all_tags := t :: !all_tags;
  if solutions then
    [ ("(* " ^ t ^ " *)"), "", (fun _ -> soltag), ns;
      ("(* /" ^ t ^ " *)"), "\n", (fun _ -> ""), ns ]
  else
    [ ("(* " ^ t ^ " *)"), ("(* /" ^ t ^ " *)"), (fun _ -> s), ns ]

let mk_droptag t =
  all_tags := t :: !all_tags;
    [ ("(* " ^ t), "*)\n", (fun _ -> ""), Soak]
  @ [ ("(* /" ^ t), "*)\n", (fun _ -> ""), Soak]

let mk_gradetag t b =
  all_tags := t :: !all_tags;
  if b then
    [ ("(** " ^ t ^ ":"), "*)\n", (fun s -> s ^ "\n"), NoSoak]
  else
    [ ("(** " ^ t ^ ":"), "*)\n", (fun _ -> ""), NoSoak]

let do_exercises =
      mk_exercises ("!A",", advanced, recommended") stars
    @ mk_exercises ("A!",", advanced, recommended") stars
    @ mk_exercises ("A?",", advanced, optional")    stars
    @ mk_exercises ("?A",", advanced, optional")    stars
    @ mk_exercises ("A", ", advanced")              stars
    @ mk_exercises ("!", ", recommended")           stars
    @ mk_exercises ("?", ", optional")              stars
    @ mk_exercises ("",  "")                        stars

let do_grading =
          mk_gradetag "GRADE" false
        @ mk_grade_thm stars false
        @ mk_grade_manual stars false
    @ mk_grade_ltac stars false

let silent_spec =
      mk_tag "HIDE" false
    @ mk_tag "SOONER" false
    @ mk_tag "LATER" false
    @ mk_tag "DISCUSS" false
    @ mk_tag "INSTRUCTORS" false
    @ mk_tag "FIX" false
    @ mk_tag "ADD" false

(* grading_spec: collection of tags used for grading *)
let grading_spec =
          do_exercises
        @ do_grading

let exercise_spec =
          do_exercises
        @ do_grading

(* spec: collection of tags used for full, terse, solutions, etc. *)

let spec =
      mk_tag "TERSE" (combined || terse)
    @ mk_tag "ADVANCED" advanced
    @ mk_tag "FULL" (combined || not terse)
    @ mk_soltag "SOLUTION" "(* FILL IN HERE *)"
    @ mk_soltag "ADMITTED" "(* FILL IN HERE *) Admitted."
    @ mk_soltag "ADMIT" "(* FILL IN HERE *) admit."
    @ mk_soltag "QUIETSOLUTION" ~soltag:"" ~ns:Soak ""
    @ (if terse then
         mk_soltag "WORKINCLASS" "(* WORK IN CLASS *) Admitted."
       else
         ["(* WORKINCLASS *)", "", (fun _ -> "(* WORKED IN CLASS *)"), NoSoak;
          "(* /WORKINCLASS *)", "\n", (fun _ -> ""), NoSoak])
    @ (if terse then
         mk_soltag "ELIDEFROMTERSE" "(* ELIDED *) Admitted."
       else
         ["(* ELIDEFROMTERSE *)", "\n", (fun _ -> ""), NoSoak;
          "(* /ELIDEFROMTERSE *)", "\n", (fun _ -> ""), NoSoak])
    @ (if terse then
         []
       else
         mk_tag "QUIZ" false)
    @
      (if solutions then [
         "(* OPEN COMMENT WHEN HIDING SOLUTIONS *)", "\n", (fun _ -> ""), NoSoak;
         "(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)", "\n", (fun _ -> ""), NoSoak;
         "(* UNCOMMENT WHEN HIDING SOLUTIONS", "/UNCOMMENT *)\n", (fun _ -> ""), NoSoak;
       ] else [
(*
         "(* OPEN COMMENT WHEN HIDING SOLUTIONS *)", "\n", (fun _ -> "(** <<\n"), NoSoak;
         "(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)", "\n", (fun _ -> ">> *)\n"), NoSoak;
*)
         "(* OPEN COMMENT WHEN HIDING SOLUTIONS *)", "\n", (fun _ -> "(* \n"), NoSoak;
         "(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)", "\n", (fun _ -> "*)\n"), NoSoak;
         "(* UNCOMMENT WHEN HIDING SOLUTIONS", "\n", (fun _ -> ""), NoSoak;
         "/UNCOMMENT *)", "\n", (fun _ -> ""), NoSoak;
       ])
        @ do_exercises
        @ do_grading
    @ (if advanced
         then []
         else mk_droptag "HIDEFROMADVANCED")
(*    @ mk_htmltag "NOW" "font" "color=\"red\"" *)
    @ mk_htmltag "NOW" "div" "style=\"background-color:lightgray; color:red; margin:10px; padding:10px; \""

(* tools to read and process tags on the input strings *)

let readchan chan =
  let nbytes = in_channel_length chan in
  let string = String.create nbytes in
  really_input chan string 0 nbytes;
  string

let findsubstring s1 s2 =
  let l1 = String.length s1 in
  let l2 = String.length s2 in
  let rec loop i =
    if i+l1 > l2 then None
    else if s1 = String.sub s2 i l1 then Some(i)
    else loop (i+1)
  in loop 0

let string_before s i =
  String.sub s 0 i

let string_after s i =
  String.sub s i ((String.length s) - i)

let string_between s i j =
  String.sub s i (j-i)
  (* off by 1? *)

let suffix = 400

let last_n s n =
  let len = String.length s in
  let c = min n len in
  String.sub s (len - c) c

let error s_from s_to prefix =
  Printf.eprintf "ERROR: \nTAG '%s'\nNOT FOLLOWED BY '%s'\nin...\n%s%s\n%!"
    s_from s_to (last_n prefix suffix) s_from;
  exit 1

let replace_from_to_with s_from s_to s_with ns s =
  let rec loop s =
    match findsubstring s_from s with
      None -> s
    | Some i ->
        let prefix = string_before s i in
        let rest = string_after s (i + String.length s_from) in
        match findsubstring s_to rest with
          None -> error s_from s_to prefix
        | Some j ->
                    let mid = string_before rest j in
            let rest' = string_after rest (j + String.length s_to) in
            let soakable =
                 (String.length rest' >= 1 && rest'.[0] = '\n')
              && (   (String.length rest' >= 2 && rest'.[1] = '\n')
                  || (last_n s_to 1 = "\n"))
              && (last_n prefix 2 = "\n\n") in
            let rest'' =
              match (ns, soakable) with
                Soak, true -> string_after rest' 1
              | _, _ -> rest' in
            prefix ^ s_with mid ^ loop rest''
  in loop s

let get_first_tag tag s =
  let (s_from, s_to, s_with, ns) = tag in
  match findsubstring s_from s with
      None -> ("","")
    | Some i ->
        let prefix = string_before s i in
        let rest = string_after s (i + String.length s_from) in
        match findsubstring s_to rest with
          None -> error s_from s_to prefix
        | Some j ->
                    let mid = string_before rest j in
                        let rest' = string_after rest (j + String.length s_to) in
                        (s_from ^ s_with mid ^ s_to ^ "\n", rest')

(* get_tagged tag s: returns the concatenation of
                the tag-modified substrings of s that are denoted by tag.
   tag (tag_type)
   s (string)
 *)
let get_tagged tag s =
  let rec loop s =
        let (tag_str, rest) = get_first_tag tag s in
        if String.length rest <= 0 then "\n"
        else tag_str ^ "\n" ^ (loop rest)
  in loop s


let apply_spec spec s = List.fold_left
        (fun r (f,t,w,ns) -> replace_from_to_with f t w ns r)
        s spec

(* Specific tags *)

let gr_code_tag =
  ( ("(* GRADE"), "*)", (fun x -> x), NoSoak )
let ex_code_tag =
  let change_with mid =
        let (ex_str,rest) = get_first_tag ("","*)", (fun x -> x), NoSoak) mid in
        let s = get_tagged gr_code_tag rest in
        ex_str ^ s
  in
  ( ("(* EX"), ("[] *)"), change_with, NoSoak )

let exlst_code_tag =
  let change_with mid =
        let (ex_str,rest) = get_first_tag("","*)", (fun x -> x), NoSoak) mid in
        ex_str ^ rest
  in
  ( ("(* EX"), ("[] *)"), change_with, NoSoak )


let sanity_check s =
  let check_for_stray_close_tags t =
    match findsubstring ("(* /" ^ t ^ " *)") s with
      None -> ()
    | Some i ->
        let prefix = string_before s i in
        Printf.eprintf
          "ERROR: \n'(* /%s *)'\nNOT PRECEDED BY '(* %s *)'\nin...\n%s\n%!"
          t t (last_n prefix suffix);
        exit 1
  in let _ = List.map check_for_stray_close_tags !all_tags in
     ()

let main () =
  let s = readchan stdin in
  let s1 = apply_spec silent_spec s in
  let s2 =
    if exerciselist then
      (* If exerciselist is on, we will only parse the exercises *)
      get_tagged exlst_code_tag s1
    else s1 in
  let spec' =
    if exerciselist then exercise_spec
    else spec in
  let s3 = List.fold_left
      (fun r (f,t,w,ns) -> replace_from_to_with f t w ns r)
       s2 spec'
  in
  sanity_check s3;
  output_string stdout s3

;; main()
