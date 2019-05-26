(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module Names      = Ser_names
module Environ    = Ser_environ
module Glob_term  = Ser_glob_term
module Constrexpr = Ser_constrexpr
module Pattern    = Ser_pattern

module Store = struct
  type t = Genintern.Store.t

  let t_of_sexp _ = CErrors.user_err Pp.(str "[GI Store: Cannot deserialize stores.")
  let sexp_of_t _ = Sexplib.Sexp.Atom "[GENINTERN STORE]"

end

type glob_sign =
  [%import: Genintern.glob_sign]
  [@@deriving sexp]

type glob_constr_and_expr =
  [%import: Genintern.glob_constr_and_expr]
  [@@deriving sexp]

type glob_constr_pattern_and_expr =
  [%import: Genintern.glob_constr_pattern_and_expr]
  [@@deriving sexp]
