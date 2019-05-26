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
(* Copyright 2016-2018 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv

module Names = Ser_names

type add_ml =
  [%import: Mltop.add_ml]
  [@@deriving sexp]

type vo_path_spec =
  [%import: Mltop.vo_path_spec]
  [@@deriving sexp]

type coq_path_spec =
  [%import: Mltop.coq_path_spec]
  [@@deriving sexp]

type coq_path =
  [%import: Mltop.coq_path]
  [@@deriving sexp]
