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

(** [process ~doc ~sid ast] is the main callback to add a new AST
   [ast] to the Coq document [doc] after [sid]. It will return the new
   Coq document and [Stateid.t] span identifier. *)
type procfun
  =  doc:Stm.doc
  -> sid:Stateid.t
  -> Vernacexpr.vernac_control CAst.t
  -> Stm.doc * Stateid.t

(** [compfun ~in_file ~in_chan ~process ~doc ~sid] is the main
   callback for user processing of Coq documents. [in_file] and
   [in_chan] will contain the name and input channel for the file to
   process, [process] is the Coq callback to add a sentence, and [doc]
   [sid] are the initial state id and document.
*)
type compfun
  =  in_file:string
  -> in_chan:in_channel
  -> process:procfun
  -> doc:Stm.doc
  -> sid:Stateid.t
  -> Stm.doc

(** [maincomp ~ext ~name ~desc ~compfun] will launch a compilation
   executable. [maincomp] will process command line options and call
   the [compfun] callback with the appropiate parameters. [ext]
   indicates the file extension to read, [name] and [desc] are used in
   the help of the executable.
*)
val maincomp
  :  ext:string
  -> name:string
  -> man:Cmdliner.Manpage.block list
  -> compfun:compfun
  -> unit
