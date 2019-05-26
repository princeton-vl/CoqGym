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

type constr_as_binder_kind = Notation_term.constr_as_binder_kind
val constr_as_binder_kind_of_sexp : Sexp.t -> constr_as_binder_kind
val sexp_of_constr_as_binder_kind : constr_as_binder_kind -> Sexp.t

type notation_var_internalization_type = Notation_term.notation_var_internalization_type
val notation_var_internalization_type_of_sexp : Sexp.t -> notation_var_internalization_type
val sexp_of_notation_var_internalization_type : notation_var_internalization_type -> Sexp.t
