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

open Ssrmatching_plugin

type cpattern =
  [%import: Ssrmatching.cpattern]

let cpattern_of_sexp o = Serlib_base.opaque_of_sexp ~typ:"Ssrmatching.cpattern" o
let sexp_of_cpattern o = Serlib_base.sexp_of_opaque ~typ:"Ssrmatching.cpattern" o

type rpattern =
  [%import: Ssrmatching.rpattern]

let rpattern_of_sexp o = Serlib_base.opaque_of_sexp ~typ:"Ssrmatching.rpattern" o
let sexp_of_rpattern o = Serlib_base.sexp_of_opaque ~typ:"Ssrmatching.rpattern" o

type ssrdir =
  [%import: Ssrmatching.ssrdir]
  [@@deriving sexp]
