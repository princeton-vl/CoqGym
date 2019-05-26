(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  syntax.v:  Inductive definition of the syntax                           *)
(*	       of lazyPCF                                                   *)
(*                                                                          *)
(*  Includes types, variables and terms                                     *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November  1993                                                          *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                 syntax.v                                 *)
(****************************************************************************)

Inductive ty : Set :=
  | nat_ty : ty (* natural numbers *)
  | bool_ty : ty (* boolean values *)
  | arr : ty -> ty -> ty.   (* function types *)

Inductive vari : Set :=
    x : nat -> vari.

Inductive tm : Set :=
  | o : tm (*  zero  *)
  | ttt : tm (*  true  *)
  | fff : tm (*  false *)
  | abs : vari -> ty -> tm -> tm (* lambda abstractions *)
  | appl : tm -> tm -> tm (* function applications *)
  | cond : tm -> tm -> tm -> tm (* if e1 then e2 else e3 *)
  | var : vari -> tm (* variables *)
  | succ : tm -> tm (* successor *)
  | prd : tm -> tm (* predecessor *)
  | is_o : tm -> tm (* zero test *)
  | Fix : vari -> ty -> tm -> tm (* fixed point operator *)
  | clos : tm -> vari -> ty -> tm -> tm.
						 (* closure, <x,[x:t->e]> *)

