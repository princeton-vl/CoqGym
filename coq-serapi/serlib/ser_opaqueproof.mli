(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib

type opaque = Opaqueproof.opaque

val sexp_of_opaque : opaque -> Sexp.t
val opaque_of_sexp : Sexp.t -> opaque

type opaquetab = Opaqueproof.opaquetab

val sexp_of_opaquetab : opaquetab -> Sexp.t
val opaquetab_of_sexp : Sexp.t -> opaquetab