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

type opaque = [%import: Opaqueproof.opaque]

let sexp_of_opaque = Serlib_base.sexp_of_opaque ~typ:"Opaqueproof.opaque"

let opaque_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Opaqueproof.opaque"

type opaquetab = [%import: Opaqueproof.opaquetab]

let sexp_of_opaquetab = Serlib_base.sexp_of_opaque ~typ:"Opaqueproof.opaquetab"

let opaquetab_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Opaqueproof.opaquetab"
