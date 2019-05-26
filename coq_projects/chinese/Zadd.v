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
(*                                  Zadd.v                                  *)
(****************************************************************************)

Require Export Arith.
Require Export Nat_complements.
Require Export Lci.
Require Export groups.
Require Export rings.
Require Export Zbase.
Require Export Z_succ_pred.

(* Addition on Z, (Z, +) is a group *)

(*Recursive Definition addZ : Z -> Z -> Z := 
       OZ        y => y
|   (pos O)      y => (succZ y)
|   (pos (S n1)) y => (succZ (addZ (pos n1) y))
|   (neg O)      y => (predZ y)
|   (neg (S n1)) y => (predZ (addZ (neg n1) y)).*)


(* this definition introduces unnecessary names *)


Fixpoint addpos (x2 : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => succZ x2
  | S n0 => succZ (addpos x2 n0)
  end.

Fixpoint addneg (x2 : Z) (n : nat) {struct n} : Z :=
  match n with
  | O => predZ x2
  | S n0 => predZ (addneg x2 n0)
  end.

Definition addZ (x1 x2 : Z) :=
  match x1 with
  | OZ => x2
  | pos n => addpos x2 n
  | neg n => addneg x2 n
  end.


Lemma addZ_eq1 : forall y : Z, addZ OZ y = y.
Proof.
auto with arith.
Qed.

Lemma addZ_eq2 : forall y : Z, addZ (pos 0) y = succZ y.
Proof.
auto with arith.
Qed.

Lemma addZ_eq3 :
 forall (n1 : nat) (y : Z), addZ (pos (S n1)) y = succZ (addZ (pos n1) y).
Proof.
auto with arith.
Qed.

Lemma addZ_eq4 : forall y : Z, addZ (neg 0) y = predZ y.
Proof.
auto with arith.
Qed.

Lemma addZ_eq5 :
 forall (n1 : nat) (y : Z), addZ (neg (S n1)) y = predZ (addZ (neg n1) y).
Proof.
auto with arith.
Qed.



(***************)
Lemma succ_addZ_l : forall x y : Z, addZ (succZ x) y = succZ (addZ x y).

intros; elim x.
(* OZ *)
reflexivity.
(* pos n *)
trivial.
(* neg n *)
simple destruct n.
(* neg O *)
simpl in |- *; symmetry  in |- *; exact (succ_predZ y). 
(* neg (S n0) *)
intros; symmetry  in |- *; rewrite addZ_eq5.
apply succ_predZ.
Qed.

(***************)
Lemma pred_addZ_l : forall x y : Z, addZ (predZ x) y = predZ (addZ x y).

intros; elim x.
(* OZ *)
reflexivity.
(* pos n *)
simple destruct n.
simpl in |- *; rewrite pred_succZ; trivial.
intros; rewrite addZ_eq3; rewrite pred_succZ; trivial.
trivial.
Qed.

(**********************)
Lemma tech_add_pos_succZ :
 forall (x : nat) (y : Z), addZ (pos (S x)) y = succZ (addZ (pos x) y).
Proof addZ_eq3.

(**********************)
Lemma tech_add_neg_predZ :
 forall (x : nat) (y : Z), addZ (neg (S x)) y = predZ (addZ (neg x) y).
Proof addZ_eq5.

(***************)
Lemma succ_addZ_r : forall x y : Z, addZ x (succZ y) = succZ (addZ x y).

intros; elim x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
(* pos O *)
reflexivity.
(* pos y0 *)
intros.
do 2 rewrite (tech_add_pos_succZ n0).
elim H; reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
simpl in |- *; symmetry  in |- *; apply succ_pred_pred_succZ.
(* neg y0 *)
intros.
do 2 rewrite (tech_add_neg_predZ n0).
rewrite H.
symmetry  in |- *; apply succ_pred_pred_succZ.
Qed.

(***************)
Lemma pred_addZ_r : forall x y : Z, addZ x (predZ y) = predZ (addZ x y).

intros; elim x.
(* OZ *)
reflexivity.
(* (pos n) *)
simple induction n.
(* (pos O) *)
simpl in |- *; apply succ_pred_pred_succZ.
(* (pos (S y0)) *)
intros.
do 2 rewrite (tech_add_pos_succZ n0).
rewrite H; apply succ_pred_pred_succZ.
(* neg n *)
simple induction n.
(* neg O *)
reflexivity.
(* neg (S y0) *)
intros.
do 2 rewrite (tech_add_neg_predZ n0).
elim H; reflexivity.
Qed.

(***********)
Lemma add_OZ : forall x : Z, addZ x OZ = x.

simple induction x.
(* OZ *)
reflexivity.
(* pos n *)
simple induction n.
reflexivity.
intros; rewrite tech_add_pos_succZ; rewrite H; reflexivity.
(* neg n *)
simple induction n.
reflexivity.
intros; rewrite tech_add_neg_predZ; rewrite H; reflexivity.
Qed.

(*****************)
Lemma add_IZ_succZ : forall x : Z, addZ x IZ = succZ x.

intros.
cut (succZ OZ = IZ); intros. elim H.
rewrite (succ_addZ_r x OZ); rewrite (add_OZ x); reflexivity.
reflexivity.
Qed.

(*****************)
Lemma add_mIZ_predZ : forall x : Z, addZ x (neg 0) = predZ x.

intros.
cut (predZ OZ = neg 0); intros. elim H.
rewrite (pred_addZ_r x OZ); rewrite (add_OZ x); reflexivity.
reflexivity.
Qed.

(*************************)
Theorem addZ_commutativity : commutativity Z addZ.

unfold commutativity in |- *; intros; elim x.
(* OZ *)
simpl in |- *; symmetry  in |- *; exact (add_OZ y).
(* pos n *)
simple induction n.
(* pos O *)
simpl in |- *; symmetry  in |- *; exact (add_IZ_succZ y).
(* pos (S y0) *)
intros; rewrite (tech_add_pos_succZ n0 y). rewrite H.
cut (succZ (pos n0) = pos (S n0)); intros. elim H0.
rewrite (succ_addZ_r y (pos n0)); reflexivity.
reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
simpl in |- *; symmetry  in |- *; exact (add_mIZ_predZ y).
(* neg (S y0) *)
intros; rewrite (tech_add_neg_predZ n0 y). rewrite H.
cut (predZ (neg n0) = neg (S n0)); intros. elim H0.
rewrite (pred_addZ_r y (neg n0)); reflexivity.
reflexivity.
Qed.

(*************************)
Lemma tech_add_pos_neg_posZ :
 forall n1 n2 : nat, n2 < n1 -> addZ (pos n1) (neg n2) = pos (n1 - S n2).

simple induction n2.
(* O *)
intros; elim (addZ_commutativity (neg 0) (pos n1)).
rewrite addZ_eq4.
elim minus_n_Sm; trivial.
elim minus_n_O.
apply tech_pred_posZ; trivial.
(* S y *)
intros; elim (addZ_commutativity (neg (S n)) (pos n1)).
rewrite tech_add_neg_predZ.
elim (addZ_commutativity (pos n1) (neg n)).
rewrite H; auto with arith.
elim (minus_n_Sm n1 (S n) H0).
apply tech_pred_posZ.
apply lt_minus2; trivial.
Qed.

(*************************)
Theorem addZ_associativity : associativity Z addZ.

unfold associativity in |- *; intros; elim x.
(* OZ *)
unfold addZ in |- *; reflexivity.
(* pos n *)
intros; elim n.
(* pos O *)
simpl in |- *; symmetry  in |- *; exact (succ_addZ_l y z).
(* pos (S y0) *)
intros.
do 2 rewrite (tech_add_pos_succZ n0).
rewrite (succ_addZ_l (addZ (pos n0) y) z); elim H; reflexivity.
(* neg n *)
simple induction n.
(* neg O *)
simpl in |- *; symmetry  in |- *; exact (pred_addZ_l y z).
(* neg (S n0) *)
intros.
do 2 rewrite (tech_add_neg_predZ n0).
rewrite (pred_addZ_l (addZ (neg n0) y) z); elim H; reflexivity.
Qed.

(************)
Definition IdZ (x : Z) := True.

(*******************)
Theorem addZ_neutral : neutral Z IdZ addZ OZ.

unfold neutral in |- *; intros.
split. exact I.
intros. split. exact (add_OZ x). unfold addZ in |- *; reflexivity.
Qed.

(*************)
Definition oppZ (x : Z) :=
  match x return Z with
  | OZ =>
      (* OZ *)  OZ
      (* pos n *) 
  | pos n => neg n
      (* neg n *) 
  | neg n => pos n
  end.

(*************)
Lemma opp_succZ : forall x : Z, oppZ (succZ x) = predZ (oppZ x).

simple destruct x.
(* OZ *)
reflexivity.
(* pos n *)
intros; reflexivity.
(* neg n *)
simple destruct n; intros; reflexivity. 
Qed.

(*************)
Lemma opp_predZ : forall x : Z, oppZ (predZ x) = succZ (oppZ x).

simple destruct x.
(* OZ *)
reflexivity.
(* pos n *)
simple destruct n; intros; reflexivity. 
(* neg n *)
intros; reflexivity.
Qed.

(*********************)
Lemma tech_add_pos_negZ : forall n : nat, addZ (pos n) (neg n) = OZ.

simple induction n.
(* O *)
reflexivity.
(* S y *)
intros; rewrite (tech_add_pos_succZ n0).
elim succ_addZ_r; exact H.
Qed.

(*********************)
Lemma tech_add_neg_posZ : forall n : nat, addZ (neg n) (pos n) = OZ.

intros; elim (addZ_commutativity (pos n) (neg n));
 exact (tech_add_pos_negZ n).
Qed.

(*********************)
Lemma tech_add_pos_posZ :
 forall n m : nat, addZ (pos n) (pos m) = pos (S (n + m)).

intros; elim n.
(* O *)
reflexivity.
(* S n0 *)
intros; rewrite (tech_add_pos_succZ n0 (pos m)); rewrite H; reflexivity.
Qed.

(*********************)
Lemma tech_add_neg_negZ :
 forall n m : nat, addZ (neg n) (neg m) = neg (S (n + m)).

simple induction n.
(* O *)
reflexivity.
(* S n0 *)
intros; rewrite (tech_add_neg_predZ n0 (neg m)); rewrite H; reflexivity.
Qed.

(********************)
Theorem addZ_opposite : opposite Z IdZ addZ OZ oppZ.

repeat split; trivial.
(* -> *)
case x.
(* OZ *)
reflexivity.
(* pos n *)
intros; exact (tech_add_pos_negZ n).
(* neg n *)
intros; exact (tech_add_neg_posZ n).
(* <- *)
case x.
(* OZ *)
reflexivity.
(* pos n *)
intros; exact (tech_add_neg_posZ n).
(* neg n *)
intros; exact (tech_add_pos_negZ n).
Qed.

(**************)
Theorem Z_group : is_group Z IdZ addZ OZ oppZ.

split.
red in |- *; trivial.
split. exact addZ_associativity.
split. exact addZ_neutral.
exact addZ_opposite.
Qed.

(********************)
Theorem abs_eq_or_oppZ : forall x : Z, {absZ x = x} + {absZ x = oppZ x}.

simple destruct x; auto with arith.
Qed.

(*********************)
Lemma tech_opp_pos_negZ :
 forall n : nat, oppZ (pos n) = neg n /\ oppZ (neg n) = pos n.

simple induction n; auto with arith.
Qed.