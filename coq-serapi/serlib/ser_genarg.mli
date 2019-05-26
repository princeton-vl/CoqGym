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

open Sexplib

(* val sexp_of_raw_tactic_expr : (Tacexpr.raw_tactic_expr -> Sexp.t) ref *)
(* val sexp_of_tacdef_body     : (Tacexpr.tacdef_body     -> Sexp.t) ref *)

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

type rlevel = Genarg.rlevel
type glevel = Genarg.glevel
type tlevel = Genarg.tlevel

val rlevel_of_sexp : Sexp.t -> rlevel
val sexp_of_rlevel : rlevel -> Sexp.t

val glevel_of_sexp : Sexp.t -> glevel
val sexp_of_glevel : glevel -> Sexp.t

val tlevel_of_sexp : Sexp.t -> tlevel
val sexp_of_tlevel : tlevel -> Sexp.t

type 'a generic_argument = 'a Genarg.generic_argument

val generic_argument_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a Genarg.generic_argument
val sexp_of_generic_argument : ('a -> Sexp.t) -> 'a Genarg.generic_argument -> Sexp.t

type glob_generic_argument = Genarg.glob_generic_argument

val glob_generic_argument_of_sexp : Sexp.t -> Genarg.glob_generic_argument
val sexp_of_glob_generic_argument : Genarg.glob_generic_argument -> Sexp.t

type raw_generic_argument = Genarg.raw_generic_argument
val raw_generic_argument_of_sexp : Sexp.t -> Genarg.raw_generic_argument
val sexp_of_raw_generic_argument : Genarg.raw_generic_argument -> Sexp.t

type typed_generic_argument = Genarg.typed_generic_argument
val typed_generic_argument_of_sexp : Sexp.t -> Genarg.typed_generic_argument
val sexp_of_typed_generic_argument : Genarg.typed_generic_argument -> Sexp.t

(* Registering serializing functions *)
type ('raw, 'glb, 'top) gen_ser =
  { raw_ser : 'raw -> Sexp.t;
    raw_des : Sexp.t -> 'raw;

    glb_ser : 'glb -> Sexp.t;
    glb_des : Sexp.t -> 'glb;

    top_ser : 'top -> Sexp.t;
    top_des : Sexp.t -> 'top;
  }

val register_genser :
  ('raw, 'glb, 'top) Genarg.genarg_type ->
  ('raw, 'glb, 'top) gen_ser -> unit

val mk_uniform : ('t -> Sexp.t) -> (Sexp.t -> 't) -> ('t,'t,'t) gen_ser

