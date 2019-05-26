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

(************************************************************************)
(* Public API for Ocaml clients                                         *)
(************************************************************************)

open Ltac_plugin
open Sexplib.Conv

(** The SerAPI Protocol *)

(**
SerAPI is

{2 History:}

{2 Basic Overview of the Protocol:}

{2 Overview of the functionality: }

{3 Document creation and checking: }

{3 Querying documents: }

{3 Advanced and experimental functionalities: }

*)

(** {2 Protocol Specification } *)

(******************************************************************************)
(* Basic Protocol Objects                                                     *)
(******************************************************************************)

(** {3 Basic Protocol Objects} *)

type coq_object =
  | CoqString    of string
  | CoqSList     of string list
  | CoqPp        of Pp.t
  (* | CoqRichpp    of Richpp.richpp *)
  | CoqLoc       of Loc.t
  | CoqTok       of Tok.t list
  | CoqAst       of Vernacexpr.vernac_control Loc.located
  | CoqOption    of Goptions.option_name * Goptions.option_state
  | CoqConstr    of Constr.constr
  | CoqExpr      of Constrexpr.constr_expr
  | CoqMInd      of Names.MutInd.t * Declarations.mutual_inductive_body
  | CoqEnv       of Environ.env
  | CoqTactic    of Names.KerName.t * Tacenv.ltac_entry
  | CoqLtac      of Tacexpr.raw_tactic_expr
  | CoqGenArg    of Genarg.raw_generic_argument
  | CoqQualId    of Libnames.qualid
  | CoqLibrary   of Library.library_location * Names.DirPath.t * CUnix.physical_path
  | CoqGlobRef   of Names.GlobRef.t
  | CoqImplicit  of Impargs.implicits_list
  | CoqProfData  of Profile_ltac.treenode
  | CoqNotation  of Constrexpr.notation
  | CoqUnparsing of Ppextend.unparsing_rule * Ppextend.extra_unparsing_rules * Notation_gram.notation_grammar
  (* | CoqPhyLoc  of Library.library_location * Names.DirPath.t * string (\* CUnix.physical_path *\) *)
  | CoqGoal      of Constr.t               Serapi_goals.reified_goal Proof.pre_goals
  | CoqExtGoal   of Constrexpr.constr_expr Serapi_goals.reified_goal Proof.pre_goals
  | CoqProof     of Goal.goal list
                    * (Goal.goal list * Goal.goal list) list
                    * Goal.goal list
                    * Goal.goal list
                    (* We don't seralize the evar map for now... *)
                    (* * Evd.evar_map *)
  | CoqAssumptions of Serapi_assumptions.t

(******************************************************************************)
(* Printing Sub-Protocol                                                      *)
(******************************************************************************)

(** {3 Printing Options} *)

(** Query output format  *)
type print_format =
  | PpSer
  (** Output in serialized format [usually sexp] *)
  | PpStr
  (** Output a string with a human-friendly representation *)
  | PpTex
  (** Output a TeX expression *)
  | PpCoq
  (** Output a Coq [Pp.t], representation-indepedent document *)
  (* | PpRichpp *)

(** Printing options, not all options are relevant for all printing backends *)
type print_opt =
  { pp_format : print_format  [@default PpSer]
  (** Output format ({e default PpSer}) *)
  ; pp_depth  : int           [@default 0]
  (** Depth  ({e default 0}) *)
  ; pp_elide  : string        [@default "..."]
  (** Elipsis ({e default: "..."}) *)
  ; pp_margin : int           [@default 72]
  (** Marging ({e default: 72}) *)
  }

(******************************************************************************)
(* Parsing Sub-Protocol                                                       *)
(******************************************************************************)

(* no public interface *)

(******************************************************************************)
(* Query Sub-Protocol                                                         *)
(******************************************************************************)

(** {3 Query Sub-Protocol } *)

(** Predicates on the queries. This is at the moment mostly a token functionality *)
type query_pred =
  | Prefix of string
  (** Filter named objects based on the given prefix *)

type query_opt =
  { preds : query_pred sexp_list;
    limit : int sexp_option;
    sid   : Stateid.t [@default Stm.get_current_state ~doc:Stm.(get_doc 0)];
    pp    : print_opt [@default { pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 } ];
    (* Legacy/Deprecated *)
    route : Feedback.route_id [@default 0];
  }

(** We would ideally make both query_cmd and coq_object depend on a
  * tag such that query : 'a query -> 'a coq_object.
  *)
type query_cmd =
  | Type       of Constr.constr
  | Option
  | Search
  | Goals                          (* Return goals [TODO: Add filtering/limiting options] *)
  | EGoals                         (* Return goals [TODO: Add filtering/limiting options] *)
  | Ast                            (* Return ast *)
  | TypeOf     of string           (* XXX Unimplemented *)
  | Names      of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  | Tactics    of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  | Locate     of string           (* argument is prefix -> XXX Move to use the prefix predicate *)
  | LocateLibrary of string
  | Implicits  of string           (* XXX Print LTAC signatures (with prefix) *)
  | Unparsing  of string           (* XXX  *)
  | Definition of string
  (** Return the definition of the given global *)
  | PNotations                     (* XXX  *)
  | ProfileData
  | Proof
  (** Return the proof object *)
  | Vernac     of string
  (** Execute an arbitrary Coq command in an isolated state. *)
  | Env
  (** Return the current enviroment *)
  | Assumptions of string
  (** Return the assumptions of given global *)

(******************************************************************************)
(* Control Sub-Protocol                                                       *)
(******************************************************************************)

(** {3 Control Sub-Protocol } *)

type parse_opt =
  { ontop  : Stateid.t sexp_option }

type add_opts = {
  lim    : int       sexp_option;
  ontop  : Stateid.t sexp_option;
  newtip : Stateid.t sexp_option;
  verb   : bool      [@default false];
}

(******************************************************************************)
(* Init / new document                                                        *)
(******************************************************************************)
type top_kind = TopLogical of Names.DirPath.t | TopPhysical of string
type newdoc_opts = {

  (* name of the top-level module *)
  top_name     : top_kind;

  (* Initial LoadPath. [XXX: Use the coq_pkg record?] *)
  iload_path   : Mltop.coq_path list sexp_option;

  (* Libs to require in STM init *)
  require_libs : (string * string option * bool option) list sexp_option;

}

(******************************************************************************)
(* Help                                                                       *)
(******************************************************************************)

(* no public interface *)

(******************************************************************************)
(* Top-Level Commands                                                         *)
(******************************************************************************)

(** {3 Top Level Protocol } *)

type cmd =
  | NewDoc     of newdoc_opts
  | Add        of add_opts  * string
  | Cancel     of Stateid.t list
  | Exec       of Stateid.t
  | Query      of query_opt * query_cmd
  | Print      of print_opt * coq_object
  | Parse      of parse_opt * string
  (* Full document checking *)
  | Join
  | Finish
  (*******************************************************************)
  (* Non-supported commands, only for convenience.                   *)
  | ReadFile   of string
  | Tokenize   of string
  (*******************************************************************)
  (* Administrativia                                                 *)
  | Noop
  | Help
  | Quit
  (*******************************************************************)

(******************************************************************************)
(* Answer Types                                                               *)
(******************************************************************************)

exception NoSuchState of Stateid.t

type answer_kind =
    Ack
  | Completed
  | Added     of Stateid.t * Loc.t * [`NewTip | `Unfocus of Stateid.t ]
  | Canceled  of Stateid.t list
  | ObjList   of coq_object list
  | CoqExn    of Loc.t option * (Stateid.t * Stateid.t) option * Printexc.raw_backtrace * exn

(** {3 Entry points to the DSL evaluator} *)

val exec_cmd : cmd -> answer_kind list

type cmd_tag = string
type tagged_cmd = cmd_tag * cmd

(* XXX: Maybe 'a answer for a parametric serializer? *)
    type answer =
    | Answer    of cmd_tag * answer_kind
    | Feedback  of Feedback.feedback

    (******************************************************************************)
    (* Global Protocol Options                                                    *)
    (******************************************************************************)

    (* type ser_opts = { *)
    (* coqlib   : string option;       (\* Whether we should load the prelude, and its location *\) *)
    (* in_chan  : in_channel;          (\* Input/Output channels                                *\) *)
    (* out_chan : out_channel; *)
    (* human    : bool; *)
    (* print0   : bool; *)
    (* lheader  : bool; *)
    (* implicit : bool; *)
    (*   async    : Sertop_init.async_flags; *)
    (* } *)
