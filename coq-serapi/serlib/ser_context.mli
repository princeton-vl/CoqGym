(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

module Rel : sig
  module Declaration : sig

    type ('c,'t) pt = ('c,'t) Context.Rel.Declaration.pt
    val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
    val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

  end

  type ('c, 't) pt = ('c,'t) Context.Rel.pt
  val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
  val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

end

module Named : sig

  module Declaration : sig

    type ('c, 't) pt = ('c, 't) Context.Named.Declaration.pt
    val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
    val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

  end

  type ('c, 't) pt = ('c, 't) Context.Named.pt
  val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
  val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

end

module Compacted : sig

  module Declaration : sig

    type ('c, 't) pt = ('c, 't) Context.Compacted.Declaration.pt
    val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
    val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

  end

  type ('c, 't) pt = ('c, 't) Context.Compacted.pt
  val pt_of_sexp : (Sexp.t -> 'c) -> (Sexp.t -> 't) -> Sexp.t -> ('c,'t) pt
  val sexp_of_pt : ('c -> Sexp.t) -> ('t -> Sexp.t) -> ('c,'t) pt -> Sexp.t

end
