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

exception Ser_error of string

let _ = CErrors.register_handler (function
    | Ser_error msg -> Pp.(seq [str "Serlib Error: "; str msg])
    | _ ->
      raise CErrors.Unhandled)

let opaque_of_sexp ~typ _obj =
  raise (Ser_error ("["^typ^": ABSTRACT / cannot deserialize]"))

let exn_on_opaque = ref true

let sexp_of_opaque ~typ _exp =
  let msg = "["^typ^": ABSTRACT]" in
  if !exn_on_opaque then
    raise (Ser_error msg)
  else
    Sexplib.Sexp.Atom ("["^typ^": ABSTRACT]")
