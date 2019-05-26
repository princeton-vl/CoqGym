(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                  Zle.v                                   *)
(****************************************************************************)
Require Export Arith.
Require Export misc.
Require Export groups.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.

(**************)
(* order on Z *)
(**************)

(************)
Definition leZ (x y : Z) :=
  match x return Prop with
  | OZ =>
      match y return Prop with
      | OZ => True
      | pos n => True
      | neg n => False
      end
  | pos n =>
      match y return Prop with
      | OZ => False
      | pos m => n <= m
      | neg m => False
      end
  | neg n =>
      match y return Prop with
      | OZ => True
      | pos m => True
      | neg m => m <= n
      end
  end.

(**************)
Lemma sign_absZ : forall x : Z, leZ OZ (absZ x).

Proof.
intros; elim x; simpl in |- *. exact I. intro; simpl in |- *. exact I. intro; simpl in |- *. exact I.
Qed.

(********************)
Lemma tech_le_pos_abs : forall x : Z, leZ OZ x -> absZ x = x.

Proof.
intros x; elim x. 
unfold absZ in |- *; reflexivity. unfold absZ in |- *; reflexivity. intros; elim H.
Qed.

(************************)
Theorem leZ_antisymmetric : antisym Z leZ.

Proof.
unfold antisym in |- *; intros x y; elim x.
(* OZ *)
elim y.
(* OZ OZ *)
reflexivity.
(* OZ (pos n) *)
intros; elim H0.
(* OZ (neg n) *)
intros; elim H.
(* (pos n) *)
intros n; elim y.
(* (pos n) OZ *)
intros; elim H.
(* (pos n) (pos n0) *)
simpl in |- *; intros; elim (le_antisym n n0 H H0); reflexivity.
(* (pos n) (neg n0) *)
intros; elim H.
(* (neg n) *)
intros n; elim y.
(* (neg n) OZ *)
intros; elim H0.
(* (neg n) (pos n0) *)
intros; elim H0.
(* (neg n) (neg n0) *)
simpl in |- *; intros; elim (le_antisym n0 n H H0); reflexivity.
Qed.

(************)
Definition ltZ (x y : Z) := leZ (succZ x) y.

(****************)
Definition lt_absZ (x y : Z) := ltZ (absZ x) (absZ y).

(*******************)
Lemma tech_lt_abs_OZ : forall x : Z, lt_absZ x (pos 0) -> x = OZ.

Proof.
simple induction x.
(* OZ *)
reflexivity.
(* pos n *)
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *;
 unfold leZ in |- *; intros. 
elim (le_Sn_O n H).
(* neg n *)
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *;
 unfold leZ in |- *; intros. 
elim (le_Sn_O n H).
Qed.

(*******************)
Lemma tech_posOZ_pos : forall n : nat, leZ OZ (posOZ n).

Proof.
intros; elim n. simpl in |- *; exact I. simpl in |- *; intros; exact I.
Qed.

(**************)
Lemma le_opp_OZ_l : forall x : Z, leZ OZ x -> leZ (oppZ x) OZ.

Proof.
intros x; elim x. simpl in |- *; intros; exact I. simpl in |- *; intros; exact I. 
intros; elim H.
Qed.

(**************)
Lemma le_opp_OZ :
 forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = OZ.

Proof.
intros. apply (leZ_antisymmetric x OZ). rewrite H. exact (le_opp_OZ_l y H1).
exact H0.
Qed.

(***************)
Lemma le_opp_OZ2 :
 forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = y.

Proof.
intros.
rewrite (le_opp_OZ x y H H0 H1). 
rewrite (opp_opp Z IdZ addZ OZ oppZ Z_group y I); elim H.
rewrite (le_opp_OZ x y H H0 H1); simpl in |- *; reflexivity.
Qed.
