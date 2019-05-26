(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std

type bigint = [%import: Bigint.bigint]

type _bigint                = Ser_Bigint of string [@@deriving sexp]

let _bigint_put  bigint             = Ser_Bigint (Bigint.to_string bigint)
let _bigint_get (Ser_Bigint bigint) = Bigint.of_string bigint

let bigint_of_sexp sexp   = _bigint_get (_bigint_of_sexp sexp)
let sexp_of_bigint bigint = sexp_of__bigint (_bigint_put bigint)
