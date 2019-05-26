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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Names
open Sexplib

module Id : sig

  type t = Id.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

  module Set : sig
    type t = Id.Set.t

    val t_of_sexp : Sexp.t -> t
    val sexp_of_t : t -> Sexp.t
  end

  module Map : sig
    type 'a t = 'a Id.Map.t
    val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
    val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
  end
end

module Name : sig

  type t = Name.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module DirPath : sig

  type t = DirPath.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Label : sig

  type t = Label.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module MBId : sig

  type t = MBId.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module ModPath : sig
  type t = ModPath.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module MPmap : sig

  type 'a t = 'a Names.MPmap.t

  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
end

module KerName : sig

  type t = KerName.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Constant : sig

  type t = Constant.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Cmap_env : sig

  type 'a t = 'a Names.Cmap_env.t

  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
end

module MutInd : sig

  type t = Names.MutInd.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

module Mindmap_env : sig

  type 'a t = 'a Names.Mindmap_env.t

  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
end

type 'a tableKey = 'a Names.tableKey

val tableKey_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a tableKey
val sexp_of_tableKey : ('a -> Sexp.t) -> 'a tableKey -> Sexp.t

type variable    = Names.variable
type inductive   = Names.inductive
type constructor = Names.constructor

module Projection : sig

  type t = Names.Projection.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

type projection  = Names.Projection.t

module GlobRef : sig

  type t = Names.GlobRef.t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

end

val variable_of_sexp : Sexp.t -> variable
val sexp_of_variable : variable -> Sexp.t

val inductive_of_sexp : Sexp.t -> inductive
val sexp_of_inductive : inductive -> Sexp.t

val constructor_of_sexp : Sexp.t -> constructor
val sexp_of_constructor : constructor -> Sexp.t

val projection_of_sexp : Sexp.t -> projection
val sexp_of_projection : projection -> Sexp.t

type evaluable_global_reference = Names.evaluable_global_reference
val evaluable_global_reference_of_sexp : Sexp.t -> evaluable_global_reference
val sexp_of_evaluable_global_reference : evaluable_global_reference -> Sexp.t

type lident = Names.lident
val lident_of_sexp : Sexp.t -> lident
val sexp_of_lident : lident -> Sexp.t

type lname = Names.lname
val lname_of_sexp : Sexp.t -> lname
val sexp_of_lname : lname -> Sexp.t

type lstring = Names.lstring
val lstring_of_sexp : Sexp.t -> lstring
val sexp_of_lstring : lstring -> Sexp.t
