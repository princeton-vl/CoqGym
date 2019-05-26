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
open Sexplib.Conv

module Level = struct
  type t = [%import: Univ.Level.t]

  type _level = ULevel of int
  [@@deriving sexp]

  let _level_put level          = ULevel (Option.default 0 (Univ.Level.var_index level))
  let _level_get (ULevel level) = Univ.Level.var level

  let t_of_sexp sexp  = _level_get (_level_of_sexp sexp)
  let sexp_of_t level = sexp_of__level (_level_put level)
end

type universe_level = Level.t
  [@@deriving sexp]

(* XXX: Think what to do with this  *)
module Universe = struct
  type t = [%import: Univ.Universe.t]

  type _t = (Level.t * int) list
  [@@deriving sexp]

  let t_of_sexp sexp     = Obj.magic (_t_of_sexp sexp)
  let sexp_of_t universe = sexp_of__t (Obj.magic universe)

end

type universe = Universe.t
  [@@deriving sexp]

(*************************************************************************)

module Instance = struct

type t =
  [%import: Univ.Instance.t]

type _instance = Instance of Level.t array
  [@@deriving sexp]

let _instance_put instance            = Instance (Univ.Instance.to_array instance)
let _instance_get (Instance instance) = Univ.Instance.of_array instance

let t_of_sexp sexp     = _instance_get (_instance_of_sexp sexp)
let sexp_of_t instance = sexp_of__instance (_instance_put instance)

end

type constraint_type =
  [%import: Univ.constraint_type]
  [@@deriving sexp]

type univ_constraint =
  [%import: Univ.univ_constraint]
  [@@deriving sexp]

module Constraint = struct

  type t = Univ.Constraint.t

  let t_of_sexp sexp =
    Univ.Constraint.of_list (list_of_sexp univ_constraint_of_sexp sexp)

  let sexp_of_t cst =
    sexp_of_list sexp_of_univ_constraint (Univ.Constraint.elements cst)

end

module Variance = struct

  type t =
    [%import: Univ.Variance.t]
    [@@deriving sexp]

end

module UContext = struct

  type t = Univ.UContext.t

  let t_of_sexp s = Univ.UContext.make (Conv.pair_of_sexp Instance.t_of_sexp Constraint.t_of_sexp s)
  let sexp_of_t t = Conv.sexp_of_pair Instance.sexp_of_t Constraint.sexp_of_t (Univ.UContext.dest t)

end

type universe_context = UContext.t
  [@@deriving sexp]

module AUContext = struct

  type t = Univ.AUContext.t

  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Univ.AUContext.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Univ.AUContext.t"

end

type abstract_universe_context = AUContext.t
  [@@deriving sexp]

module CumulativityInfo = struct

  type t = Univ.CumulativityInfo.t

  let t_of_sexp s = Univ.CumulativityInfo.make (Conv.pair_of_sexp universe_context_of_sexp (array_of_sexp Variance.t_of_sexp) s)
  let sexp_of_t t =
    Conv.sexp_of_pair sexp_of_universe_context
      (sexp_of_array Variance.sexp_of_t) Univ.CumulativityInfo.(univ_context t, variance t)

end

type cumulativity_info = CumulativityInfo.t
  [@@deriving sexp]

module ACumulativityInfo = struct

  type t = Univ.ACumulativityInfo.t

  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Univ.ACumulativityInfo.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Univ.ACumulativityInfo.t"

end

module ContextSet = struct

  type t = Univ.ContextSet.t

  let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Univ.ContextSet.t"
  let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"Univ.ContextSet.t"

end

type abstract_cumulativity_info = ACumulativityInfo.t
  [@@deriving sexp]

type universe_instance =
  [%import: Univ.universe_instance]
  [@@deriving sexp]

type 'a puniverses =
  [%import: 'a Univ.puniverses]
  [@@deriving sexp]

type explanation =
  [%import: Univ.explanation]
  [@@deriving sexp]

(* This problem seems due to packing in OCaml 4.07.0 *)
module Stdlib = struct
module Lazy = struct

  type 'a t = 'a Lazy.t
  let t_of_sexp = lazy_t_of_sexp
  let sexp_of_t = sexp_of_lazy_t

end
end

(* For 4.06.0 *)
module Lazy = Stdlib.Lazy

type univ_inconsistency =
  [%import: Univ.univ_inconsistency]
  [@@deriving sexp]

