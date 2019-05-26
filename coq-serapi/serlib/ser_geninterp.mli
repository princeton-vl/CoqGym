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
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

module Val : sig

  type t = Geninterp.Val.t

  (* val t_of_sexp : Sexp.t -> t *)
  val sexp_of_t : t -> Sexp.t
  val t_of_sexp : Sexp.t -> t

end

type interp_sign = Geninterp.interp_sign
val interp_sign_of_sexp : Sexp.t -> interp_sign
val sexp_of_interp_sign : interp_sign -> Sexp.t
