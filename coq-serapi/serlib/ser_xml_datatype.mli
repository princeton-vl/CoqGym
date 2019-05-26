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

type 'a gxml = 'a Xml_datatype.gxml

val gxml_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a gxml
val sexp_of_gxml : ('a -> Sexp.t) -> 'a gxml -> Sexp.t

type xml = Xml_datatype.xml

val xml_of_sexp : Sexp.t -> xml
val sexp_of_xml : xml -> Sexp.t
