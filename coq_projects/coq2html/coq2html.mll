(* *********************************************************************)
(*                                                                     *)
(*              The Coq2HTML documentation generator                   *)
(*                                                                     *)
(*                   Xavier Leroy, INRIA Paris                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.                                *)
(*                                                                     *)
(* *********************************************************************)

{
open Printf

(** Cross-referencing *)

let current_module = ref ""

(* Record cross-references found in .glob files *)

type xref =
  | Def of string * string    (* path, type *)
  | Ref of string * string * string (* unit, path, type *)

(* (name of module, character position in file) -> cross-reference *)
let xref_table : (string * int, xref) Hashtbl.t = Hashtbl.create 273

(* Records all module names for which a .glob file is given *)
let xref_modules : (string, unit) Hashtbl.t = Hashtbl.create 29

let path sp id =
  match sp, id with
  | "<>", "<>" -> ""
  | "<>", _    -> id
  | _   , "<>" -> sp
  | _   , _    -> sp ^ "." ^ id

let add_module m =
  (*eprintf "add_module %s\n" m;*)
  Hashtbl.add xref_modules m ()

let add_reference curmod pos dp sp id ty =
  (*eprintf "add_reference %s %d %s %s %s %s\n" curmod pos dp sp id ty;*)
  if not (Hashtbl.mem xref_table (curmod, pos))
  then Hashtbl.add xref_table (curmod, pos) (Ref(dp, path sp id, ty))

let add_definition curmod pos sp id ty =
  if not (Hashtbl.mem xref_table (curmod, pos))
  then Hashtbl.add xref_table (curmod, pos) (Def(path sp id, ty))

(* Map module names to URLs *)

let coqlib_url = "http://coq.inria.fr/library/"

(* logical name with final '.' -> absolute or relative URL *)
let documentation_urls : (string * string) list ref = ref [("Coq.", coqlib_url)]

let add_documentation_url logicalname url =
  documentation_urls := (logicalname ^ ".", url) :: !documentation_urls

let starts_with s x =
  let ls = String.length s and lx = String.length x in
  ls >= lx && String.sub s 0 lx = x

let ends_with s x =
  let ls = String.length s and lx = String.length x in
  ls >= lx && String.sub s (ls - lx) lx = x

let url_concat url suff =
  (if ends_with url "/" then url else url ^ "/") ^ suff

let url_for_module m =
  (*eprintf "url_for_module %s\n" m;*)
  let rec url_for = function
  | [] ->
      if Hashtbl.mem xref_modules m then m ^ ".html" else raise Not_found
  | (pref, url) :: rem ->
      if starts_with m pref then url_concat url m ^ ".html" else url_for rem
  in url_for !documentation_urls

(* Produce a HTML link if possible *)

type link = Link of string | Anchor of string | Nolink

let re_sane_path = Str.regexp "[A-Za-z0-9_.]+$"

let crossref m pos =
  (*eprintf "crossref %s %d\n" m pos;*)
  try match Hashtbl.find xref_table (m, pos) with
  | Def(p, _) ->
      Anchor p
  | Ref(m', p, _) ->
      let url = url_for_module m' in  (* can raise Not_found *)
      if p = "" then
        Link url
      else if Str.string_match re_sane_path p 0 then
        Link(url ^ "#" ^ p)
      else
        Nolink
  with Not_found ->
    Nolink

(** Keywords, etc *)

module StringSet = Set.Make(String)

let mkset l = List.fold_right StringSet.add l StringSet.empty

let coq_keywords = mkset [
  "forall"; "match"; "as"; "in"; "return"; "with"; "end"; "let";
  "dest"; "fun"; "if"; "then"; "else"; "Prop"; "Set"; "Type"; ":=";
  "where"; "struct"; "wf"; "measure";
  "AddPath"; "Axiom"; "Abort"; "Boxed"; "Chapter"; "Check";
  "Coercion"; "CoFixpoint"; "CoInductive"; "Corollary"; "Defined";
  "Definition"; "End"; "Eval"; "Example"; "Export"; "Fact"; "Fix";
  "Fixpoint"; "Global"; "Grammar"; "Goal"; "Hint"; "Hypothesis";
  "Hypotheses"; "Resolve"; "Unfold"; "Immediate"; "Extern";
  "Implicit"; "Import"; "Inductive"; "Infix"; "Lemma"; "Let"; "Load";
  "Local"; "Ltac"; "Module"; "Module Type"; "Declare Module";
  "Include"; "Mutual"; "Parameter"; "Parameters"; "Print"; "Proof";
  "Qed"; "Record"; "Recursive"; "Remark"; "Require";
  "Save"; "Scheme"; "Induction"; "for"; "Sort"; "Section"; "Show";
  "Structure"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; "Set";
  "Types"; "Undo"; "Unset"; "Variable"; "Variables"; "Context";
  "Notation"; "Reserved"; "Tactic"; "Delimit"; "Bind"; "Open";
  "Scope"; "Boxed"; "Unboxed"; "Inline"; "Implicit Arguments"; "Add";
  "Strict"; "Typeclasses"; "Instance"; "Global Instance"; "Class";
  "Instantiation"; "subgoal"; "Program"; "Example"; "Obligation";
  "Obligations"; "Solve"; "using"; "Next"; "Instance"; "Equations";
  "Equations_nocomp"
]

let coq_tactics = mkset [
  "intro"; "intros"; "apply"; "rewrite"; "refine"; "case"; "clear";
  "injection"; "elimtype"; "progress"; "setoid_rewrite"; "destruct";
  "destruction"; "destruct_call"; "dependent"; "elim";
  "extensionality"; "f_equal"; "generalize"; "generalize_eqs";
  "generalize_eqs_vars"; "induction"; "rename"; "move"; "omega";
  "set"; "assert"; "do"; "repeat"; "cut"; "assumption"; "exact";
  "split"; "subst"; "try"; "discriminate"; "simpl"; "unfold"; "red";
  "compute"; "at"; "in"; "by"; "reflexivity"; "symmetry";
  "transitivity"; "replace"; "setoid_replace"; "inversion";
  "inversion_clear"; "pattern"; "intuition"; "congruence"; "fail";
  "fresh"; "trivial"; "exact"; "tauto"; "firstorder"; "ring";
  "clapply"; "program_simpl"; "program_simplify"; "eapply"; "auto";
  "eauto"
]

(** HTML generation *)

let oc = ref stdout

let character = function
  | '<' -> output_string !oc "&lt;"
  | '>' -> output_string !oc "&gt;"
  | '&' -> output_string !oc "&amp;"
  |  c  -> output_char !oc c

let section_level = function
  | "*" -> 1
  | "**" -> 2
  | _ -> 3

let start_section sect =
  fprintf !oc "<h%d>" (section_level sect)
let end_section sect =
  fprintf !oc "</h%d>\n" (section_level sect)

let start_doc_right () =
  fprintf !oc "<span class=\"docright\">(* "
let end_doc_right () =
  fprintf !oc " *)</span>"

let enum_depth = ref 0

let  set_enum_depth d =
  if !enum_depth < d then begin
    fprintf !oc "<ul>\n";
    fprintf !oc "<li>\n";
    incr enum_depth;
  end
  else if !enum_depth > d then begin
    fprintf !oc "</li>\n";
    fprintf !oc "</ul>\n";
    decr enum_depth;
  end
  else if !enum_depth > 0 then begin
    fprintf !oc "</li>\n";
    fprintf !oc "<li>\n"
  end

let start_doc () =
  fprintf !oc "<div class=\"doc\">"
let end_doc () =
  set_enum_depth 0;
  fprintf !oc "</div>\n"

let ident pos id =
  if StringSet.mem id coq_keywords then
    fprintf !oc "<span class=\"kwd\">%s</span>" id
  else if StringSet.mem id coq_tactics then
    fprintf !oc "<span class=\"tactic\">%s</span>" id
  else match crossref !current_module pos with
  | Nolink ->
      fprintf !oc "<span class=\"id\">%s</span>" id
  | Link p ->
      fprintf !oc "<span class=\"id\"><a href=\"%s\">%s</a></span>" p id
  | Anchor p ->
      fprintf !oc "<span class=\"id\"><a name=\"%s\">%s</a></span>" p id

let space s =
  for _ = 1 to String.length s do fprintf !oc "&nbsp;" done

let newline () =
  fprintf !oc "<br/>\n"

let dashes = function
  | "-" -> set_enum_depth 1
  | "--" -> set_enum_depth 2
  | "---" -> set_enum_depth 3
  | "----" -> set_enum_depth 4
  | _ -> fprintf !oc "<hr/>\n"

let start_verbatim () =
  fprintf !oc "<pre>\n"

let end_verbatim () =
  fprintf !oc "</pre>\n"

let start_comment () =
  fprintf !oc "<span class=\"comment\">(*"

let end_comment () =
  fprintf !oc "*)</span>"

let start_bracket () =
  fprintf !oc "<span class=\"bracket\">"

let end_bracket () =
  fprintf !oc "</span>"

let in_proof = ref false
let proof_counter = ref 0

let start_proof kwd =
  in_proof := true;
  incr proof_counter;
  fprintf !oc
  "<div class=\"toggleproof\" onclick=\"toggleDisplay('proof%d')\">%s</div>\n"
    !proof_counter kwd;
  fprintf !oc "<div class=\"proofscript\" id=\"proof%d\">\n" !proof_counter

let end_proof kwd =
  fprintf !oc "%s</div>\n" kwd;
  in_proof := false

(* Like Str.global_replace but don't interpret '\1' etc in replacement text *)
let global_replace re subst txt =
  Str.global_substitute re (fun _ -> subst) txt
  
let start_html_page modname =
  output_string !oc
    (global_replace (Str.regexp "\\$NAME") modname Resources.header)

let end_html_page () =
  output_string !oc Resources.footer

}

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let path = ident ("." ident)*
let start_proof = ("Proof" space* ".") | ("Proof" space+ "with") | ("Next" space+ "Obligation.")
let end_proof = "Qed." | "Defined." | "Save." | "Admitted." | "Abort."

let xref = ['A'-'Z' 'a'-'z' '0'-'9' '_' '.']+ | "<>"
let integer = ['0'-'9']+

rule coq_bol = parse
  | space* (start_proof as sp)
      { start_proof sp;
        skip_newline lexbuf }
  | space* "(** " ("*"+ as sect)
      { start_section sect;
        doc lexbuf;
        end_section sect;
        skip_newline lexbuf }
  | space* "(** "
      { start_doc();
        doc lexbuf;
        end_doc();
        skip_newline lexbuf }
  | (space* as s) "(*"
      { if !in_proof then (space s; start_comment());
	comment lexbuf;
        if !in_proof then coq lexbuf else skip_newline lexbuf }
  | eof
      { () }
  | space* as s
      { space s;
        coq lexbuf }

and skip_newline = parse
  | space* "\n"
      { coq_bol lexbuf }
  | ""
      { coq lexbuf }

and coq = parse
  | end_proof as ep
      { end_proof ep;
        skip_newline lexbuf }
  | "(**r "
      { start_doc_right();
        doc lexbuf;
        end_doc_right();
        coq lexbuf }
  | "(*"
      { if !in_proof then start_comment();
        comment lexbuf;
        coq lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; coq lexbuf }
  | "\n"
      { newline(); coq_bol lexbuf }
  | eof
      { () }
  | _ as c
      { character c; coq lexbuf }

and bracket = parse
  | ']'
      { () }
  | '['
      { character '['; bracket lexbuf; character ']'; bracket lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; bracket lexbuf }
  | eof
      { () }
  | _ as c
      { character c; bracket lexbuf }

and comment = parse
  | "*)"
      { if !in_proof then end_comment() }
  | "(*"
      { if !in_proof then start_comment();
        comment lexbuf; comment lexbuf }
  | eof
      { () }
  | "\n"
      { if !in_proof then newline();
        comment lexbuf }
  | space* as s
      { if !in_proof then space s;
        comment lexbuf }
  | eof
      { () }
  | _ as c
      { if !in_proof then character c;
        comment lexbuf }

and doc_bol = parse
  | "<<" space* "\n"
      { start_verbatim();
        verbatim lexbuf;
        end_verbatim();
        doc_bol lexbuf }
  | "-"+ as d
      { dashes d; doc lexbuf }
  | "\n"
      { set_enum_depth 0; doc_bol lexbuf }
  | ""
      { doc lexbuf }

and doc = parse
  | "*)"
      { () }
  | "\n"
      { character '\n'; doc_bol lexbuf }
  | "["
      { start_bracket(); bracket lexbuf; end_bracket(); doc lexbuf }
  | "#" ([^ '\n' '#']* as html) "#"
      { output_string !oc html; doc lexbuf }
  | eof
      { () }
  | _ as c
      { character c; doc lexbuf }

and verbatim = parse
  | "\n>>" space* "\n"
      { () }
  | eof
      { () }
  | _ as c
      { character c; verbatim lexbuf }

and globfile = parse
  | eof
      { () }
  | "F" (path as m) space* "\n"
      { current_module := m; add_module m;
        globfile lexbuf }
  | "R" (integer as pos) ":" (integer)
    space+ (xref as dp)
    space+ (xref as sp)
    space+ (xref as id)
    space+ (ident as ty)
    space* "\n"
      { add_reference !current_module (int_of_string pos) dp sp id ty;
        globfile lexbuf }
  | (ident as ty)
    space+ (integer as pos) ":" (integer)
    space+ (xref as sp)
    space+ (xref as id)
    space* "\n"
      { add_definition !current_module (int_of_string pos) sp id ty;
        globfile lexbuf }
  | [^ '\n']* "\n"
      { globfile lexbuf }

{

let make_redirect fromfile toURL =
  let oc = open_out fromfile in
  output_string oc
    (global_replace (Str.regexp "\\$URL") toURL Resources.redirect);
  close_out oc

let output_dir = ref Filename.current_dir_name
let logical_name_base = ref ""
let generate_css = ref true
let use_short_names = ref false
let generate_redirects = ref false

let module_name_of_file_name f =
  let components = Str.split (Str.regexp "/") f in
  String.concat "." (List.filter (fun s -> s <> "." && s <> "..") components)

let process_v_file f =
  let pref_f = Filename.chop_suffix f ".v" in
  let base_f = Filename.basename pref_f in
  let module_name = !logical_name_base ^ module_name_of_file_name pref_f in
  current_module := module_name;
  let friendly_name = if !use_short_names then base_f else module_name in
  let ic = open_in f in
  oc := open_out (Filename.concat !output_dir (module_name ^ ".html"));
  start_html_page friendly_name;
  coq_bol (Lexing.from_channel ic);
  end_html_page();
  close_out !oc; oc := stdout;
  close_in ic;
  if !generate_redirects && !logical_name_base <> "" then
    make_redirect (Filename.concat !output_dir (base_f ^ ".html"))
                  (module_name ^ ".html")

let process_glob_file f =
  current_module := "";
  let ic = open_in f in
  globfile (Lexing.from_channel ic);
  close_in ic

let write_file txt filename =
  let oc = open_out filename in
  output_string oc txt;
  close_out oc
  
let _ =
  let v_files = ref [] and glob_files = ref [] in
  let process_file f =
    if Filename.check_suffix f ".v" then
      v_files := f :: !v_files
    else if Filename.check_suffix f ".glob" then
      glob_files := f :: !glob_files
    else begin
      eprintf "Don't know what to do with file %s\n" f; exit 2
    end in
  Arg.parse (Arg.align [
    "-base", Arg.String (fun s -> logical_name_base := s ^ "."),
      "<coqdir>  Set the name space for the modules being processed";
    "-coqlib", Arg.String (fun s -> add_documentation_url "Coq" s),
      "<url>   Set base URL for Coq standard library";
    "-d", Arg.Set_string output_dir,
      "<dir>   Output files to directory <dir> (default: current directory)";
    "-external",
      (let x = ref "" in
       Arg.Tuple [
         Arg.Set_string x;
         Arg.String (fun y -> add_documentation_url y !x)
       ]),
      "<url> <coqdir> Set base URL for linking references whose names start with <coqdir>";
    "-no-css", Arg.Clear generate_css,
      "   Do not add coq2html.css to the output directory";
    "-redirect", Arg.Set generate_redirects,
      "   Generate redirection files modname.html -> coqdir.modname.html";
    "-short-names", Arg.Set use_short_names,
      "   Use short, unqualified module names in the output"
  ])
  process_file
  "Usage: coq2html [options] file.glob ... file.v ...\nOptions are:";
  if !v_files = [] then begin
    eprintf "No .v file provided, aborting\n";
    exit 2
  end;
  if (try not (Sys.is_directory !output_dir) with Sys_error _ -> true)
  then begin
    eprintf "Error: output directory %s does not exist or is not a directory.\n" !output_dir;
    exit 2
  end;
  List.iter process_glob_file (List.rev !glob_files);
  List.iter process_v_file (List.rev !v_files);
  write_file Resources.js (Filename.concat !output_dir "coq2html.js");
  if !generate_css then
    write_file Resources.css (Filename.concat !output_dir "coq2html.css")
}
