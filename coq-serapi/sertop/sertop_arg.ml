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

open Cmdliner

[@@@ocaml.warning "-44-45"]
let prelude =
  let doc = "Load Coq.Init.Prelude from $(docv); plugins/ and theories/ should live there." in
  Arg.(value & opt string Coq_config.coqlib & info ["coqlib"] ~docv:"COQPATH" ~doc)

let async =
  let doc = "Enable async support using Coq binary $(docv) (experimental)." in
  Arg.(value & opt (some string) None & info ["async"] ~doc ~docv:"COQTOP")

let quick =
  let doc = "Skip checking opaque proofs (very experimental)." in
  Arg.(value & flag & info ["quick"] ~doc)

let async_full =
  let doc = "Enable Coq's async_full option." in
  Arg.(value & flag & info ["async-full"] ~doc)

let deep_edits =
  let doc = "Enable Coq's deep document edits option." in
  Arg.(value & flag & info ["deep-edits"] ~doc)

let async_workers =
  let doc = "Maximum number of async workers." in
  Arg.(value & opt int 3 & info ["async-workers"] ~doc)

let implicit_stdlib =
  let doc = "Allow loading unqualified stdlib libraries (deprecated)." in
  Arg.(value & flag & info ["implicit"] ~doc)

let print_args = let open Sertop_ser in
  Arg.(enum ["sertop", SP_Sertop; "human", SP_Human; "mach", SP_Mach])

let print_args_doc = Arg.doc_alts
  ["sertop, a custom printer (UTF-8 with emacs-compatible quoting)";
   "human, sexplib's human-format printer (recommended for debug sessions)";
   "mach, sexplib's machine-format printer"
  ]

let printer =
  let open Sertop_ser in
  (* XXX Must improve argument information *)
  (* let doc = "Select S-expression printer." in *)
  Arg.(value & opt print_args SP_Sertop & info ["printer"] ~doc:print_args_doc)

let debug =
  let doc = "Enable debug mode for Coq." in
  Arg.(value & flag & info ["debug"] ~doc)

let print0 =
  let doc = "End responses with a \\\\0 char." in
  Arg.(value & flag & info ["print0"] ~doc)

let length =
  let doc = "Emit a byte-length header before output. (deprecated)." in
  Arg.(value & flag & info ["length"] ~doc)

(* We handle the conversion here *)

let no_init =
  let doc = "Omits the creation of a new document; this means the user \
             will have to call `(NewDoc ...)` before Coq can be used \
             and set there the proper loadpath, requires, ..." in
  Arg.(value & flag & info ["no_init"] ~doc)

let coq_lp_conv ~implicit (unix_path,lp) = Mltop.{
    path_spec = VoPath {
        coq_path  = Libnames.dirpath_of_string lp;
        unix_path;
        has_ml    = AddRecML;
        implicit;
      };
    recursive = true;
  }

let rload_path : Mltop.coq_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR and implicitly open its namespace." in
  Term.(const List.(map (coq_lp_conv ~implicit:true)) $
        Arg.(value & opt_all (pair dir string) [] & info ["R"; "rec-load-path"] ~docv:"DIR,LP"~doc))

let load_path : Mltop.coq_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Term.(const List.(map (coq_lp_conv ~implicit:false)) $
        Arg.(value & opt_all (pair dir string) [] & info ["Q"; "load-path"] ~docv:"DIR,LP" ~doc))

let coq_include_conv unix_path = Mltop.{
    path_spec = MlPath unix_path;
    recursive = false;
  }

let ml_include_path : Mltop.coq_path list Term.t =
  let doc = "Include DIR in default loadpath, for locating ML files" in
  Term.(const List.(map coq_include_conv) $
        Arg.(value & opt_all dir [] & info ["I"; "ml-include-path"] ~docv:"DIR" ~doc))

(* Low-level serialization options for display *)
let omit_loc : bool Term.t =
  let doc = "[debug option] shorten location printing" in
  Arg.(value & flag & info ["omit_loc"] ~doc)

let omit_att : bool Term.t =
  let doc = "[debug option] omit attribute nodes" in
  Arg.(value & flag & info ["omit_att"] ~doc)

let exn_on_opaque : bool Term.t =
  let doc = "[debug option] raise an exception on non-serializeble terms" in
  Arg.(value & flag & info ["exn_on_opaque"] ~doc)

(* sertop options *)
type comp_mode = | C_parse | C_stats | C_print | C_sexp | C_check | C_vo

let comp_mode_args =
  Arg.(enum
         [ "parse", C_parse
         ; "stats", C_stats
         ; "print", C_print
         ; "sexp",  C_sexp
         ; "check", C_check
         ; "vo",    C_vo])

let comp_mode_doc = Arg.doc_alts
  [ "parse: parse the file and remain silent (except for Coq output)"
  ; "stats: output stats on the input file"
  ; "print: output using the Coq pretty printer"
  ;  "sexp: output serialized version of the input file"
  ; "check: check proofs in the file and remain silent (except for Coq output)"
  ;    "vo: check proofs and output .vo version of the input file"
  ]

let comp_mode =
  Arg.(value & opt comp_mode_args C_parse & info ["mode"] ~doc:comp_mode_doc)

