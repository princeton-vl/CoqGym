(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*  NF.v                                                                    *)
(*                                                                          *)
(*  This file contains a definition of the normal forms                     *)
(*  of evaluation and some properties which are used in                     *)
(*  later proofs.                                                           *)
(*                                                                          *)
(*                                                                          *)
(*  Jill Seaman                                                             *)
(*  Coq V5.8                                                                *)
(*  November 1993                                                           *)
(*                                                                          *)
(*                                                                          *)
(****************************************************************************)
(*                                   NF.v                                   *)
(****************************************************************************)

Require Import syntax.

(********************************************************)
(*							*)
(*	If <<e,A>> -> <<e',A'>>                  	*)
(*	then e' belongs to the following set:		*)
(*							*)
(*	NF = ttt | fff | S | F 				*)
(*           where					*)
(*		S = o | (succ S) 			*)
(*		F = (abs x t e) | (clos F x t e)	*)
(*							*)
(*	which corresponds to:				*)
(*	NF = 0 | true | false | succn(0) | F		*)
(*	 F = \x:t.e | <F,[x:t->e]>			*)
(*							*)
(********************************************************)

Inductive F : tm -> Prop :=
  | F_abs : forall (v : vari) (s : ty) (e : tm), F (abs v s e)
  | F_clos : forall (e e1 : tm) (v : vari) (s : ty), F e -> F (clos e v s e1).
Inductive Sno : tm -> Prop :=
  | Sno_o : Sno o
  | Sno_s : forall e : tm, Sno e -> Sno (succ e).

Inductive NF : tm -> Prop :=
  | NF_ttt : NF ttt
  | NF_fff : NF fff
  | NF_Sno : forall e : tm, Sno e -> NF e
  | NF_F : forall e : tm, F e -> NF e.

(********************************************************)
(*							*)
(*   The inverse of NF_Sno and Sno_s are proved here    *)
(*	and used in a later proof.  They require        *)
(*	predicates about (succ e) for inductive proofs. *)
(*							*)
(********************************************************)

Definition NFsucc (e : tm) :=
  match e return Prop with
  | o =>
      (* o *)  True
      (* ttt *) 
  | ttt => True
      (* fff *) 
  | fff => True
      (* abs v s e *) 
  | abs v s e => True
      (* appl e1 e2 *) 
  | appl e1 e2 => True
      (* cond e1 e2 e3 *)
  | cond e1 e2 e3 => True
      (* var v *) 
  | var v => True
      (* succ n *) 
  | succ n => Sno (succ n)
      (* prd n *) 
  | prd n => True
      (* is_o n *) 
  | is_o n => True
      (* fix v s e *) 
  | Fix v s e => True
      (* clos e v s e1 *)
  | clos e v s e1 => True
  end.

Goal forall e : tm, NF (succ e) -> Sno (succ e).
intros e HNF.  change (NFsucc (succ e)) in |- *.
elim HNF; simpl in |- *; intros; exact I || elim H; simpl in |- *; intros;
 exact I || apply Sno_s; assumption.
Save inv_NF_Sno.


Definition SnoSucc (e : tm) :=
  match e return Prop with
  | o =>
      (* o *)  True
      (* ttt *) 
  | ttt => True
      (* fff *) 
  | fff => True
      (* abs v s e *) 
  | abs v s e => True
      (* appl e1 e2 *) 
  | appl e1 e2 => True
      (* cond e1 e2 e3 *) 
  | cond e1 e2 e3 => True
      (* var v *) 
  | var v => True
      (* succ n *) 
  | succ n => Sno n
      (* prd n *) 
  | prd n => True
      (* is_o n *) 
  | is_o n => True
      (* fix v s e *) 
  | Fix v s e => True
      (* clos e v s e1 *) 
  | clos e v s e1 => True
  end.

Goal forall e : tm, Sno (succ e) -> Sno e.
intros e HSno. change (SnoSucc (succ e)) in |- *.
elim HSno; simpl in |- *; intros; exact I || assumption.
Save inv_Sno_s.