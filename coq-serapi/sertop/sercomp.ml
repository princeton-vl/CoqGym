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

let compfun ~in_file ~in_chan ~process ~doc ~sid =

  let in_strm = Stream.of_channel in_chan in
  let in_pa   = Pcoq.Parsable.make ~file:(Loc.InFile in_file) in_strm in

  let stt = ref (doc, sid) in
  try while true do
      let doc, sid = !stt in
      let east = Stm.parse_sentence ~doc sid in_pa in
      stt := process ~doc ~sid east
    done;
    fst !stt
  with Stm.End_of_input -> fst !stt

let _ =
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq compiler with serialization support.";
    `S "USAGE";
    `P "To serialize `fun.v` in directory `fs` with path `Funs`:";
    `Pre "sercomp -Q fs,Funs --mode=sexp fs/fun.v > fs/fun.sexp";
    `P "See the documentation on the project's webpage for more information"
  ]
  in
  Sercomp_lib.maincomp ~ext:".v" ~name:"sercomp" ~man ~compfun
