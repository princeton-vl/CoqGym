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

type level = Conv_oracle.level
val level_of_sexp : Sexp.t -> level
val sexp_of_level : level -> Sexp.t

type oracle = Conv_oracle.oracle
val oracle_of_sexp : Sexp.t -> oracle
val sexp_of_oracle : oracle -> Sexp.t
