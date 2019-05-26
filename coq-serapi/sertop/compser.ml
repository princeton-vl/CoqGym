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
(* Written by: Emilio J. Gallego Arias / Karl Palmskog                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

let compfun ~in_file:_ ~in_chan ~process ~doc ~sid =

  let stt = ref (doc, sid) in
  try while true; do
      let line = input_line in_chan in
      let doc, sid = !stt in
      if String.trim line <> "" then
        let sxp = Sexplib.Sexp.of_string line in
        let ast = Ser_cAst.t_of_sexp Ser_vernacexpr.vernac_control_of_sexp sxp in
        stt := process ~doc ~sid ast
    done;
    fst !stt
  with End_of_file -> fst !stt

let _ =
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq compiler with deserialization support.";
    `S "USAGE";
    `P "To deserialize and check `fun.sexp` in directory `fs` with path `Funs`:";
    `Pre "compser -Q fs,Funs --mode=check fs/fun.sexp";
    `P "See the documentation on the project's webpage for more information"
  ]
  in
  Sercomp_lib.maincomp ~ext:".sexp" ~name:"compser" ~man ~compfun
