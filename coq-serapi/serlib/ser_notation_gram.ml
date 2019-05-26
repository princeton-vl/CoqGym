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

open Sexplib.Conv

module Names         = Ser_names
module Constrexpr    = Ser_constrexpr
module Tok           = Ser_tok
module Extend        = Ser_extend

type precedence =
  [%import: Notation_gram.precedence]
  [@@deriving sexp]

type parenRelation =
  [%import: Notation_gram.parenRelation]
  [@@deriving sexp]

type tolerability =
  [%import: Notation_gram.tolerability]
  [@@deriving sexp]

type grammar_constr_prod_item =
  [%import: Notation_gram.grammar_constr_prod_item]
  [@@deriving sexp]

type level =
  [%import: Notation_gram.level]
  [@@deriving sexp]

type one_notation_grammar =
  [%import: Notation_gram.one_notation_grammar]
  [@@deriving sexp]

type notation_grammar =
  [%import: Notation_gram.notation_grammar]
  [@@deriving sexp]
