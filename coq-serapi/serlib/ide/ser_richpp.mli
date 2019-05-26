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

open Sexplib

type richpp = Richpp.richpp

val richpp_of_sexp : Sexp.t -> Richpp.richpp
val sexp_of_richpp : Richpp.richpp -> Sexp.t

type 'a located = 'a Richpp.located

val located_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a Richpp.located
val sexp_of_located : ('a -> Sexp.t) -> 'a Richpp.located -> Sexp.t
