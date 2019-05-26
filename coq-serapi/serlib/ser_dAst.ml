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

(* We force the thunks in serialization *)

open Sexplib

module CAst = Ser_cAst

type ('a, 'b) thunk = [%import: ('a,'b) DAst.thunk]

let sexp_of_thunk : type a b. (a -> Sexp.t) -> (b -> Sexp.t) -> (a,b) thunk -> Sexp.t =
  fun f _ t -> match t with
  | Value v -> f v
  | Thunk t -> f (Lazy.force t)

let thunk_of_sexp : type a b. (Sexp.t -> a) -> (Sexp.t -> b) -> Sexp.t -> (a,b) thunk =
  fun f _ s -> Value (f s)

type ('a, 'b) t =
  [%import: ('a, 'b) DAst.t]
  [@@deriving sexp]
