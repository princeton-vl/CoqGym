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

open Sexplib.Std

(* Id: private *)
type t = [%import: Stateid.t]

type _stateid                = int [@@deriving sexp]
(* type _stateid             = Ser_Stateid of int [@@deriving sexp] *)

let _stateid_put stateid = (Stateid.to_int stateid)
let _stateid_get stateid = Stateid.of_int stateid

let t_of_sexp sexp    = _stateid_get (_stateid_of_sexp sexp)
let sexp_of_t stateid = sexp_of__stateid (_stateid_put stateid)
