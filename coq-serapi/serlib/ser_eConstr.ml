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

(* open Sexplib *)
(* open Sexplib.Std *)

module Constr  = Ser_constr
module Environ = Ser_environ

type t = EConstr.t
let t_of_sexp s = EConstr.of_constr (Ser_constr.constr_of_sexp s)
let sexp_of_t c = Ser_constr.sexp_of_constr (EConstr.Unsafe.to_constr c)

type existential =
  [%import: EConstr.existential]
  [@@deriving sexp]

type constr =
  [%import: EConstr.constr]
  [@@deriving sexp]

type types =
  [%import: EConstr.types]
  [@@deriving sexp]

type unsafe_judgment =
  [%import: EConstr.unsafe_judgment]
  [@@deriving sexp]

