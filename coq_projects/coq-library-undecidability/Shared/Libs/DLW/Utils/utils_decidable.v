(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Max Omega Wellfounded Bool.

Require Import list_focus utils_tac utils_list utils_nat.

Set Implicit Arguments.

(** We show that unbounded decidable predicates are exactly
    the direct images of strictly increasing sequences nat -> nat 

    Hence, this gives an easy construction of the sequence
    of all primes ...

*)

Section sinc_decidable.

  Variable (P : nat -> Prop)
           (f : nat -> nat) 
           (Hf : forall n, f n < f (S n))
           (HP : forall n, P n <-> exists k, n = f k).

  Let f_mono x y : x <= y -> f x <= f y.
  Proof.
    induction 1 as [ | y H IH ]; auto.
    apply le_trans with (1 := IH), lt_le_weak, Hf.
  Qed.

  Let f_smono x y : x < y -> f x < f y.
  Proof.
    intros H; apply f_mono in H.
    apply lt_le_trans with (2 := H), Hf.
  Qed.

  Let f_ge_n n : n <= f n.
  Proof.
    induction n as [ | n IHn ]; try omega.
    apply le_trans with (2 := Hf _); omega.
  Qed.

  Let unbounded n : exists k, n <= k /\ P k.
  Proof. exists (f n); split; auto; rewrite HP; exists n; auto. Qed.

  Let decidable n : { P n } + { ~ P n }.
  Proof.
    destruct (@bounded_search (S n) (fun i => f i = n))
      as [ (i & H1 & H2) | H1 ].
    + intros i _; destruct (eq_nat_dec (f i) n); tauto.
    + left; rewrite HP; eauto.
    + right; rewrite HP; intros (k & Hk).
      symmetry in Hk; generalize Hk; apply H1.
      rewrite <- Hk; apply le_n_S; auto.
  Qed.

  Theorem sinc_decidable : (forall n, exists k, n <= k /\ P k)
                         * (forall n, { P n } + { ~ P n }).
  Proof. split; auto. Qed.

End sinc_decidable.

Section decidable_sinc.

  Variable (P    : nat -> Prop)
           (Punb : forall n, exists k, n <= k /\ P k)
           (Pdec : forall n, { P n } + { ~ P n }).

  Let next n : { k | P k /\ n <= k /\ forall x, P x -> x < n \/ k <= x }.
  Proof.
    destruct min_dec with (P := fun k => P k /\ n <= k)
      as (k & (H1 & H2) & H3).
    + intros i; destruct (Pdec i); destruct (le_lt_dec n i); try tauto; right; intro; omega.
    + destruct (Punb (S n)) as (k & H1 & H2).
      exists k; split; auto; omega.
    + exists k; repeat (split; auto).
      intros x Hx.
      destruct (le_lt_dec n x); try omega.
      right; apply H3; auto.
  Qed.

  Let f := fix f n := match n with 
    | 0   => proj1_sig (next 0)
    | S n => proj1_sig (next (S (f n)))
  end.

  Let f_sinc n : f n < f (S n).
  Proof.
    simpl.
    destruct (next (S (f n))) as (?&?&?&?); auto.
  Qed.

  Let f_select x : { n | f n <= x < f (S n) } + { x < f 0 }.
  Proof.
    induction x as [ | x IHx ].
    + destruct (eq_nat_dec 0 (f 0)) as [ H | H ].
      * left; exists 0; rewrite H at 2 3; split; auto.
      * right; omega.
    + destruct IHx as [ (n & Hn) | Hx ].
      * destruct (eq_nat_dec (S x) (f (S n))) as [ H | H ].
        - left; exists (S n); rewrite H; split; auto.
        - left; exists n; omega.
      * destruct (eq_nat_dec (S x) (f 0)) as [ H | H ].
        - left; exists 0; rewrite H; split; auto.
        - right; omega.
  Qed.
 
  Let f_P n : P n <-> exists k, n = f k.
  Proof.
    split.
    + intros Hn.
      destruct (f_select n) as [ (k & Hk) | C ].
      * simpl in Hk.
        destruct (next (S (f k))) as (m & H1 & H2 & H3); simpl in Hk.
        apply H3 in Hn.
        destruct Hn as [ Hn | Hn ]; try omega.
        exists k; omega.
      * simpl in C.
        destruct (next 0) as (m & H1 & H2 & H3); simpl in C.
        apply H3 in Hn; omega.
    + intros (k & Hk); subst.
      induction k as [ | k IHk ]; simpl.
      * destruct (next 0) as (m & H1 & H2 & H3); simpl; auto.
      * destruct (next (S (f k))) as (m & H1 & H2 & H3); simpl; auto.
  Qed.

  Theorem decidable_sinc : { f | (forall n, f n < f (S n))
                              /\ (forall n, P n <-> exists k, n = f k) }.
  Proof. exists f; auto. Qed.

End decidable_sinc.
   
Check sinc_decidable.
Check decidable_sinc.

