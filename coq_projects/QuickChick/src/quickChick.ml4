open Ltac_plugin
open Pp
open Names
open Entries
open Declare
open Libnames
open Util
open Constrintern
open Constrexpr
open Error
open Stdarg

let message = "QuickChick"
let mk_ref s = CAst.make @@ CRef (qualid_of_string s, None)

(* Names corresponding to QuickChick's .v files *)
let show = mk_ref "QuickChick.Show.show"
let quickCheck = mk_ref "QuickChick.Test.quickCheck"
let quickCheckWith = mk_ref "QuickChick.Test.quickCheckWith"
let mutateCheck = mk_ref "QuickChick.MutateCheck.mutateCheck"
let mutateCheckWith = mk_ref "QuickChick.MutateCheck.mutateCheckWith"
let mutateCheckMany = mk_ref "QuickChick.MutateCheck.mutateCheckMany"
let mutateCheckManyWith = mk_ref "QuickChick.MutateCheck.mutateCheckManyWith"
let sample = mk_ref "QuickChick.GenLow.GenLow.sample"

(* Locate QuickChick's files *)
(* The computation is delayed because QuickChick's libraries are not available
when the plugin is first loaded. *)
(* For trunk and forthcoming Coq 8.5: *)
let qid = Libnames.make_qualid (DirPath.make [Id.of_string "QuickChick"]) (Id.of_string "QuickChick")
			       (*
let qid = qualid_of_string "QuickChick.QuickChick"
				*)
let path =
  lazy (let (_,_,path) = Library.locate_qualified_library ~warn:false qid in path)
let path = lazy (Filename.dirname (Lazy.force path))

(* [mkdir -p]: recursively make the parent directories if they do not exist. *)
let rec mkdir_ dname =
  let cmd () = Unix.mkdir dname 0o755 in
  try cmd () with
  | Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  | Unix.Unix_error (Unix.ENOENT, _, _) ->
    (* If the parent directory doesn't exist, try making it first. *)
    mkdir_ (Filename.dirname dname);
    cmd ()

(* Interface with OCaml compiler *)
let temp_dirname =
  let dname = Filename.(concat (get_temp_dir_name ()) "QuickChick") in
  mkdir_ dname;
  Filename.set_temp_dir_name dname;
  dname

(* let link_files = ["quickChickLib.cmx"]*)
let link_files = []

(* TODO: in Coq 8.5, fetch OCaml's path from Coq's configure *)
(* FIX: There is probably a more elegant place to put this flag! *)
let ocamlopt = "ocamlopt -unsafe-string"
let ocamlc = "ocamlc -unsafe-string"

let comp_ml_cmd fn out =
  let path = Lazy.force path in
  let link_files = List.map (Filename.concat path) link_files in
  let link_files = String.concat " " link_files in
  Printf.sprintf "%s -rectypes -w a -I %s -I %s %s %s -o %s" ocamlopt
    (Filename.dirname fn) path link_files fn out

(*
let comp_mli_cmd fn =
  Printf.sprintf "%s -rectypes -I %s %s" ocamlc (Lazy.force path) fn
 *)

let comp_mli_cmd fn =
  let path = Lazy.force path in
  let link_files = List.map (Filename.concat path) link_files in
  let link_files = String.concat " " link_files in
  Printf.sprintf "%s -rectypes -w a -I %s -I %s %s %s" ocamlopt
    (Filename.dirname fn) path link_files fn


let fresh_name n =
    let base = Id.of_string n in

  (** [is_visible_name id] returns [true] if [id] is already
      used on the Coq side. *)
    let is_visible_name id =
      try
        ignore (Nametab.locate (Libnames.qualid_of_ident id));
        true
      with Not_found -> false
    in
    (** Safe fresh name generation. *)
    Namegen.next_ident_away_from base is_visible_name

(** [define c] introduces a fresh constant name for the term [c]. *)
let define c env evd =
  let (evd,_) = Typing.type_of env evd c in
  let uctxt = UState.context (Evd.evar_universe_context evd) in
  let fn = fresh_name "quickchick" in
  (* TODO: Maxime - which of the new internal flags should be used here? The names aren't as clear :) *)
  ignore (declare_constant ~internal:InternalTacticRequest fn
      (DefinitionEntry (definition_entry ~univs:(Polymorphic_const_entry uctxt) (EConstr.to_constr evd c)),
       Decl_kinds.IsDefinition Decl_kinds.Definition));
  fn

(* [$TMP/QuickChick/$TIME/QuickChick.ml],
   where [$TIME] is the current time in format [HHMMSS]. *)
let new_ml_file () =
  let tm = Unix.localtime (Unix.time ()) in
  let ts = Printf.sprintf "%02d%02d%02d" tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec in
  let temp_dir = Filename.concat temp_dirname ts in
  mkdir_ temp_dir;
  Filename.temp_file ~temp_dir "QuickChick" ".ml"

let define_and_run c env evd =
  (** Extract the term and its dependencies *)
  let main = define c env evd in
  let mlf = new_ml_file () in
  let execn = Filename.chop_extension mlf in
  let mlif = execn ^ ".mli" in
  let warnings = CWarnings.get_flags () in
  let mute_extraction = warnings ^ (if warnings = "" then "" else ",") ^ "-extraction-opaque-accessed" in
  CWarnings.set_flags mute_extraction;
  Flags.silently (Extraction_plugin.Extract_env.full_extraction (Some mlf)) [qualid_of_ident main];
  CWarnings.set_flags warnings;
  (** Add a main function to get some output *)
  let oc = open_out_gen [Open_append;Open_text] 0o666 mlf in
  let for_output =
    "\nlet _ = print_string (\n" ^
    "let l = (" ^ (Id.to_string main) ^ ") in\n"^
    "let s = Bytes.create (List.length l) in\n" ^
    "let rec copy i = function\n" ^
    "| [] -> s\n" ^
    "| c :: l -> Bytes.set s i c; copy (i+1) l\n" ^
    "in Bytes.to_string (copy 0 l))" in
  Printf.fprintf oc "%s" for_output;
  close_out oc;
  (* Before compiling, remove stupid cyclic dependencies like "type int = int".
     TODO: Generalize (.) \g1\b or something *)
  let perl_cmd = "perl -i -p0e 's/type int =\\s*int/type tmptmptmp = int\\ntype int = tmptmptmp/sg' " ^ mlf in
  if Sys.command perl_cmd <> 0 then
    CErrors.user_err (str ("perl script hack failed. Report: " ^ perl_cmd)  ++ fnl ());
  (** Compile the extracted code *)
  (** Extraction sometimes produces ML code that does not implement its interface.
      We circumvent this problem by erasing the interface. **)
  Sys.remove mlif;
  (* TODO: Maxime, thoughts? *)
  (** LEO: However, sometimes the inferred types are too abstract. So we touch the .mli to close the weak types. **)
  let _exit_code = Sys.command ("touch " ^ mlif) in
  (*
  Printf.printf "Extracted ML file: %s\n" mlf;
  Printf.printf "Compile command: %s\n" (comp_ml_cmd mlf execn);
  flush_all ();
  *)
  (* Compile the (empty) .mli *)
  if Sys.command (comp_mli_cmd mlif) <> 0 then CErrors.user_err (str "Could not compile mli file" ++ fnl ());
  if Sys.command (comp_ml_cmd mlf execn) <> 0 then
    (CErrors.user_err (str "Could not compile test program" ++ fnl ()); None)

  (** Run the test *)
  else
    (* Should really be shared across this and the tool *)
    let chan = Unix.open_process_in execn in
    let builder = ref [] in
    let rec process_otl_aux () =
      let e = input_line chan in
      print_endline e;
      builder := e :: !builder;
      process_otl_aux() in
    try process_otl_aux ()
    with End_of_file ->
         let stat = Unix.close_process_in chan in
         begin match stat with
         | Unix.WEXITED 0 ->
            ()
         | Unix.WEXITED i ->
            CErrors.user_err (str (Printf.sprintf "Exited with status %d" i) ++ fnl ())
         | Unix.WSIGNALED i ->
            CErrors.user_err (str (Printf.sprintf "Killed (%d)" i) ++ fnl ())
         | Unix.WSTOPPED i ->
            CErrors.user_err (str (Printf.sprintf "Stopped (%d)" i) ++ fnl ())
         end;
         let output = String.concat "\n" (List.rev !builder) in
         Some output

(*
    (** If we want to print the time spent in tests *)
(*    let execn = "time " ^ execn in *)
    if Sys.command execn <> 0 then
      CErrors.user_err (str "Could not run test" ++ fnl ())
 *)

(* TODO: clean leftover files *)
let runTest c env evd =
  (** [c] is a constr_expr representing the test to run,
      so we first build a new constr_expr representing
      show c **)
  let c = CAst.make @@ CApp((None,show), [(c,None)]) in
  (** Build the kernel term from the const_expr *)

  (*  Printf.printf "Before interp constr\n"; flush stdout; *)
  
  let (c,_evd) = interp_constr env evd c in

  (* Printf.printf "So far so good?\n"; flush stdout; *)
  define_and_run c env evd

let run f args =
  begin match args with
  | qc_text :: _ -> Printf.printf "QuickChecking %s\n"
                      (Pp.string_of_ppcmds (Ppconstr.pr_constr_expr qc_text));
                      flush_all()
  | _ -> failwith "run called with no arguments"
  end;
  let args = List.map (fun x -> (x,None)) args in
  let c = CAst.make @@ CApp((None,f), args) in
  let env = Global.env () in
  let evd = Evd.from_env env in
  ignore (runTest c env evd)

let set_debug_flag (flag_name : string) (mode : string) =
  let toggle =
    match mode with
    | "On"  -> true
    | "Off" -> false
  in
  let reference =
    match flag_name with
    | "Debug" -> flag_debug
(*    | "Warn"  -> flag_warn
    | "Error" -> flag_error *)
  in
  reference := toggle 
(*  Libobject.declare_object
    {(Libobject.default_object ("QC_debug_flag: " ^ flag_name)) with
       cache_function = (fun (_,(flag_name, mode)) -> reference flag_name := toggle mode);
       load_function = (fun _ (_,(flag_name, mode)) -> reference flag_name := toggle mode)}
 *)
	  (*
let run_with f args p =
  let c = CApp(dummy_loc, (None,f), [(args,None);(p,None)]) in
  runTest c
	   *)

VERNAC COMMAND EXTEND QuickCheck CLASSIFIED AS SIDEFF
  | ["QuickCheck" constr(c)] ->     [run quickCheck [c]]
  | ["QuickCheckWith" constr(c1) constr(c2)] ->     [run quickCheckWith [c1;c2]]
END;;

VERNAC COMMAND EXTEND QuickChick CLASSIFIED AS SIDEFF
  | ["QuickChick" constr(c)] ->     [run quickCheck [c]]
  | ["QuickChickWith" constr(c1) constr(c2)] ->     [run quickCheckWith [c1;c2]]
END;;

VERNAC COMMAND EXTEND MutateCheck CLASSIFIED AS SIDEFF
  | ["MutateCheck" constr(c1) constr(c2)] ->     [run mutateCheck [c1;c2]]
  | ["MutateCheckWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckWith [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateChick CLASSIFIED AS SIDEFF
  | ["MutateChick" constr(c1) constr(c2)] ->     [run mutateCheck [c1;c2]]
  | ["MutateChickWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckWith [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateCheckMany CLASSIFIED AS SIDEFF
  | ["MutateCheckMany" constr(c1) constr(c2)] ->     [run mutateCheckMany [c1;c2]]
  | ["MutateCheckManyWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckMany [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND MutateChickMany CLASSIFIED AS SIDEFF
  | ["MutateChickMany" constr(c1) constr(c2)] ->     [run mutateCheckMany [c1;c2]]
  | ["MutateChickManyWith" constr(c1) constr(c2) constr(c3)] ->     [run mutateCheckMany [c1;c2;c3]]
END;;

VERNAC COMMAND EXTEND QuickChickDebug CLASSIFIED AS SIDEFF
  | ["QuickChickDebug" ident(s1) ident(s2)] ->
     [ let s1' = Id.to_string s1 in
       let s2' = Id.to_string s2 in
       set_debug_flag s1' s2' ]
END;;

VERNAC COMMAND EXTEND Sample CLASSIFIED AS SIDEFF
  | ["Sample" constr(c)] -> [run sample [c]]
END;;
