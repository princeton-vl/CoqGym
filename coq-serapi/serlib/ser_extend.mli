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

type side = Extend.side
val side_of_sexp : Sexp.t -> side
val sexp_of_side : side -> Sexp.t

type gram_assoc = Extend.gram_assoc
val gram_assoc_of_sexp : Sexp.t -> gram_assoc
val sexp_of_gram_assoc : gram_assoc -> Sexp.t

type gram_position = Extend.gram_position
val gram_position_of_sexp : Sexp.t -> gram_position
val sexp_of_gram_position : gram_position -> Sexp.t

type production_position = Extend.production_position
val production_position_of_sexp : Sexp.t -> production_position
val sexp_of_production_position : production_position -> Sexp.t

type production_level = Extend.production_level
val production_level_of_sexp : Sexp.t -> production_level
val sexp_of_production_level : production_level -> Sexp.t

type binder_entry_kind = Extend.binder_entry_kind
val binder_entry_kind_of_sexp : Sexp.t -> binder_entry_kind
val sexp_of_binder_entry_kind : binder_entry_kind -> Sexp.t

type 'lev constr_entry_key_gen = 'lev Extend.constr_entry_key_gen
val constr_entry_key_gen_of_sexp : (Sexp.t -> 'lev) ->
  Sexp.t -> 'lev constr_entry_key_gen
val sexp_of_constr_entry_key_gen : ('lev -> Sexp.t) ->
  'lev constr_entry_key_gen -> Sexp.t

type constr_entry_key = Extend.constr_entry_key
val constr_entry_key_of_sexp : Sexp.t -> constr_entry_key
val sexp_of_constr_entry_key : constr_entry_key -> Sexp.t

type constr_prod_entry_key = Extend.constr_prod_entry_key
val constr_prod_entry_key_of_sexp : Sexp.t -> constr_prod_entry_key
val sexp_of_constr_prod_entry_key : constr_prod_entry_key -> Sexp.t

type simple_constr_prod_entry_key = Extend.simple_constr_prod_entry_key

val simple_constr_prod_entry_key_of_sexp :
  Sexp.t -> simple_constr_prod_entry_key

val sexp_of_simple_constr_prod_entry_key :
  simple_constr_prod_entry_key -> Sexp.t

