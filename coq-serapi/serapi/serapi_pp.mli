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

(** This module includes all of sertop custom Format-based printers
    for Coq datatypes.

    We may want to split it into a library at some point and replace
    parts of Coq printing/
*)

type 'a pp = Format.formatter -> 'a -> unit

val pp_str      :                            string   pp
val pp_opt      :                'a pp -> ('a option) pp
val pp_list     : ?sep:string -> 'a pp -> ('a list)   pp

val pp_stateid  : Stateid.t         pp
val pp_feedback : Feedback.feedback pp
val pp_xml      : Xml_datatype.xml  pp
