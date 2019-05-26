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

open Cmdliner

let sertop_version = Ser_version.ser_git_version
let sertop printer print0 debug lheader coq_path ml_path no_init lp1 lp2 std_impl async async_full deep_edits async_workers omit_loc omit_att exn_on_opaque =

  let open  Sertop_init         in
  let open! Sertop_sexp         in

  Serlib_init.init ~omit_loc ~omit_att ~exn_on_opaque;

  let loadpath = Serapi_paths.coq_loadpath_default ~implicit:std_impl ~coq_path @
                 ml_path @ lp1 @ lp2 in

  ser_loop
    {  in_chan  = stdin;
       out_chan = stdout;

       debug;
       printer;
       print0;
       lheader;

       no_init;
       loadpath;

       async = {
         enable_async = async;
         async_full = async_full;
         deep_edits = deep_edits;
         async_workers = async_workers;
       }
    }

let sertop_cmd =
  let open Sertop_arg in
  let doc = "SerAPI Coq Toplevel" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq Toplevel with Serialization Support";
    `S "USAGE";
    `P "To build a Coq document, use the `Add` command:";
    `Pre "(Add () \"Lemma addn0 n : n + 0. Proof. now induction n. Qed.\")";
    `P "SerAPI will parse and split the document into \"logical\" sentences.";
    `P "Then, you can ask Coq to check the proof with `Exec`:";
    `Pre "(Exec 5)";
    `P "Other queries are also possible; some examples:";
    `Pre "(Query ((sid 4)) Ast)";
    `P "Will print the AST at sentence 4.";
    `Pre "(Query ((sid 3)) Goals)";
    `P "Will print the goals at sentence 3.";
    `P "See the documentation on the project's webpage for more information"
  ]
  in
  Term.(const sertop
        $ printer $ print0 $ debug $ length $ prelude $ ml_include_path $ no_init $ load_path $ rload_path $ implicit_stdlib
        $ async $ async_full $ deep_edits $ async_workers $ omit_loc $ omit_att $ exn_on_opaque ),
  Term.info "sertop" ~version:sertop_version ~doc ~man

let main () =
  match Term.eval sertop_cmd with
  | `Error _ -> exit 1
  | _        -> exit 0

let _ = main ()
