Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import List ZArith Tactics.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

(* TODO rename this file to util.v -- not only for nats *)

Lemma max_lub_l_ssr n m p:
  max n m < p -> n < p.
Proof.
  move /ltP/PeanoNat.Nat.max_lub_lt_iff => [/ltP H1 _].
  assumption.
Qed.

Lemma max_lub_r_ssr n m p:
  max n m < p -> m < p.
Proof.
  move /ltP/PeanoNat.Nat.max_lub_lt_iff => [_ /ltP H1].
  assumption.
Qed.

Lemma max_lub_ssr n m p :
  n < p -> m < p -> max n m < p.
Proof.
  move => /ltP H1 /ltP H2.
  apply/ltP/PeanoNat.Nat.max_lub_lt; eassumption.
Qed.

(* TODO do implicits for the rest of the file *)

Set Implicit Arguments.
Unset Strict Implicit.


Lemma lt0_False :
  forall n, ~ n < 0.
Proof.
  firstorder.
Qed.

Lemma leq_ltS n m :
  n <= m -> n < m.+1.
Proof.
  eauto.
Qed.

Lemma ltS_leq n m :
  n <= m -> n < m.+1.
Proof.
  eauto.
Qed.

Lemma plus_leq_compat_l n m k :
  n <= m ->
  n <= m + k.
Proof. 
  intros. ssromega.
Qed.

Lemma plus_leq_compat_r n m k :
  n <= k ->
  n <= m + k.
Proof. 
  intros. ssromega.
Qed.

Lemma leq_refl: forall n, n <= n.
Proof.
  intros. ssromega.
Qed.

Lemma succ_neq_zero :
  forall x, S x <> 0.
Proof.
  firstorder.
Qed.

Lemma isSomeSome {A : Type} (y : A) :
  Some y.
Proof.
  exact isT.
Qed.

Lemma eq_symm {A : Type} (x y : A) :
  x = y -> y = x.
Proof.
  firstorder.
Qed.

Lemma ltn0Sn_pair {A : Type} (n : nat) (g : A)  :
  0 < (n.+1, g).1.
Proof.
  ssromega.
Qed.

(* Yikes this is stupid, find a workaround *)
(* Leo, can you make me a real prop and a real forall in the plugin?? *)
Definition prop := Prop.

Definition all (A : Type) (f : A -> Prop) : Prop := forall (x : A), f x.

