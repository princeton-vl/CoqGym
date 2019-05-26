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

module Loc        = Ser_loc

module L = struct
type 'a t = {
  v   : 'a;
  loc : Loc.t option;
} [@@deriving sexp]
end

type 'a t = 'a CAst.t = private {
  v   : 'a;
  loc : Loc.t option;
}

let t_of_sexp f s = let { L.v ; loc } = L.t_of_sexp f s in CAst.make ?loc:loc v
let sexp_of_t f { CAst.v ; loc } = L.sexp_of_t f { L.v ; loc }

let omit_att = ref false

let sexp_of_t f x =
  if !omit_att then f x.CAst.v else sexp_of_t f x
