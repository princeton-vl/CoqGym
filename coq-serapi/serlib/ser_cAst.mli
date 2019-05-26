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

type 'a t = 'a CAst.t = private {
  v   : 'a;
  loc : Loc.t option;
}

val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t

val omit_att : bool ref
