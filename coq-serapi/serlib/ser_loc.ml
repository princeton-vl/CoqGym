(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(**********************************************************************)
(* Loc.mli                                                            *)
(**********************************************************************)

open Sexplib.Std

type source =
  [%import: Loc.source]
  [@@deriving sexp]

type t =
  [%import: Loc.t]
  [@@deriving sexp]

let omit_loc = ref false
let sexp_of_t x =
  if !omit_loc then Sexplib.Sexp.Atom "[LOC]" else sexp_of_t x

(* located: public *)
type 'a located =
  [%import: 'a Loc.located]
  [@@deriving sexp]
