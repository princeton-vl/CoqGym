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
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std

module Loc        = Ser_loc
module Names      = Ser_names
module Locus      = Ser_locus
module Constrexpr = Ser_constrexpr
module Genintern  = Ser_genintern
module Geninterp  = Ser_geninterp

module Ssrmatching_plugin = struct
  module Ssrmatching = Ser_ssrmatching
end

module Ltac_plugin = struct
  module Tacexpr = Ser_tacexpr
end

(* What a hack is ssreflect using... *)
module Proofview = struct
  type 'a tactic = 'a Proofview.tactic
  let tactic_of_sexp _ = Serlib_base.opaque_of_sexp ~typ:"Ssrast.tactic"
  let sexp_of_tactic _ = Serlib_base.sexp_of_opaque ~typ:"Ssrast.tactic"
end

type ssrhyp =
  [%import: Ssrast.ssrhyp]
  [@@deriving sexp]

type ssrhyp_or_id =
  [%import: Ssrast.ssrhyp_or_id]
  [@@deriving sexp]

type ssrhyps =
  [%import: Ssrast.ssrhyps]
  [@@deriving sexp]

type ssrdir =
  [%import: Ssrast.ssrdir]
  [@@deriving sexp]

type ssrsimpl =
  [%import: Ssrast.ssrsimpl]
  [@@deriving sexp]

type ssrmmod =
  [%import: Ssrast.ssrmmod]
  [@@deriving sexp]

type ssrmult =
  [%import: Ssrast.ssrmult]
  [@@deriving sexp]

type ssrocc =
  [%import: Ssrast.ssrocc]
  [@@deriving sexp]

type ssrindex =
  [%import: Ssrast.ssrindex]
  [@@deriving sexp]

type ssrclear =
  [%import: Ssrast.ssrclear]
  [@@deriving sexp]

type ssrdocc =
  [%import: Ssrast.ssrdocc]
  [@@deriving sexp]

type ssrtermkind =
  [%import: Ssrast.ssrtermkind]
  [@@deriving sexp]

type ssrterm =
  [%import: Ssrast.ssrterm]
  [@@deriving sexp]

type ast_closure_term =
  [%import: Ssrast.ast_closure_term]
  [@@deriving sexp]

type ssrview =
  [%import: Ssrast.ssrview]
  [@@deriving sexp]

type anon_iter =
  [%import: Ssrast.anon_iter]
  [@@deriving sexp]

type ssripat =
  [%import: Ssrast.ssripat]
  [@@deriving sexp]
and ssripats =
  [%import: Ssrast.ssripats]
  [@@deriving sexp]
and ssripatss =
  [%import: Ssrast.ssripatss]
  [@@deriving sexp]

type ssrhpats =
  [%import: Ssrast.ssrhpats]
  [@@deriving sexp]

type ssrhpats_wtransp =
  [%import: Ssrast.ssrhpats_wtransp]
  [@@deriving sexp]

type ssrintrosarg =
  [%import: Ssrast.ssrintrosarg]
  [@@deriving sexp]

type ssrfwdid =
  [%import: Ssrast.ssrfwdid]
  [@@deriving sexp]

type 'term ssrbind =
  [%import: 'term Ssrast.ssrbind]
  [@@deriving sexp]

type ssrbindfmt =
  [%import: Ssrast.ssrbindfmt]
  [@@deriving sexp]

type 'term ssrbindval =
  [%import: 'term Ssrast.ssrbindval]
  [@@deriving sexp]

type ssrfwdkind =
  [%import: Ssrast.ssrfwdkind]
  [@@deriving sexp]

type ssrfwdfmt =
  [%import: Ssrast.ssrfwdfmt]
  [@@deriving sexp]

type ssrclseq =
  [%import: Ssrast.ssrclseq]
  [@@deriving sexp]

type 'tac ssrhint =
  [%import: 'tac Ssrast.ssrhint]
  [@@deriving sexp]

type 'tac fwdbinders =
  [%import: 'tac Ssrast.fwdbinders]
  [@@deriving sexp]

type clause =
  [%import: Ssrast.clause]
  [@@deriving sexp]

type clauses =
  [%import: Ssrast.clauses]
  [@@deriving sexp]

type wgen =
  [%import: Ssrast.wgen]
  [@@deriving sexp]

type 'a ssrdoarg =
  [%import: 'a Ssrast.ssrdoarg]
  [@@deriving sexp]

type 'a ssrseqarg =
  [%import: 'a Ssrast.ssrseqarg]
  [@@deriving sexp]

type 'a ssragens =
  [%import: 'a Ssrast.ssragens]
  [@@deriving sexp]

type ssrapplyarg =
  [%import: Ssrast.ssrapplyarg]
  [@@deriving sexp]

type 'a ssrcasearg =
  [%import: 'a Ssrast.ssrcasearg]
  [@@deriving sexp]

type 'a ssrmovearg =
  [%import: 'a Ssrast.ssrmovearg]
  [@@deriving sexp]
