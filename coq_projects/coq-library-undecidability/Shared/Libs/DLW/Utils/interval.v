(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia.

Set Implicit Arguments.

Section interval.

  (** A small interval & valuation library *)

  Definition interval := (nat * nat)%type. (* (a,b) <~~~> [a,b[ *)

  Implicit Types (i j : interval).

  Definition in_interval i x := let (a,b) := i in a <= x < b.
  Definition out_interval i x := let (a,b) := i in x < a \/ b <= x.
  Definition interval_disjoint i j := forall x, in_interval i x -> in_interval j x -> False.

  Definition interval_union (i j : interval) :=
    match i, j with (a1,b1),(a2,b2) => (min a1 a2, max b1 b2) end.

  Fact in_out_interval i x : in_interval i x -> out_interval i x -> False.
  Proof. destruct i; simpl; lia. Qed.

  Fact in_out_interval_dec i x : { in_interval i x } + { out_interval i x }.
  Proof. 
    destruct i as (a,b); simpl.
    destruct (le_lt_dec a x); destruct (le_lt_dec b x); try (left; lia);right; lia.
  Qed. 

  Fact interval_union_left i j x : in_interval i x -> in_interval (interval_union i j) x.
  Proof.
    revert i j; intros (a,b) (u,v); simpl.
    generalize (Nat.le_min_l a u) (Nat.le_max_l b v); lia.
  Qed.

  Fact interval_union_right i j x : in_interval j x -> in_interval (interval_union i j) x.
  Proof.
    revert i j; intros (a,b) (u,v); simpl.
    generalize (Nat.le_min_r a u) (Nat.le_max_r b v); lia.
  Qed.

  Definition valuation_union i1 (g1 : nat -> nat) i2 g2 : 
               interval_disjoint i1 i2 
            -> { g | (forall x, in_interval i1 x -> g x = g1 x)
                  /\ (forall x, in_interval i2 x -> g x = g2 x) }.
  Proof.
    intros H2.
    exists (fun x => if in_out_interval_dec i1 x then g1 x else g2 x).
    split; intros x Hx.
    + destruct (in_out_interval_dec i1 x) as [ | H3 ]; auto.
      exfalso; revert Hx H3; apply in_out_interval.
    + destruct (in_out_interval_dec i1 x) as [ H3 | ]; auto.
      exfalso; revert H3 Hx; apply H2.
  Qed.

  Definition valuation_one_union k v i1 (g1 : nat -> nat) i2 g2 : 
               ~ in_interval (interval_union i1 i2) k 
            -> interval_disjoint i1 i2 
            -> { g | g k = v /\ (forall x, in_interval i1 x -> g x = g1 x)
                             /\ (forall x, in_interval i2 x -> g x = g2 x) }.
  Proof.
    intros H1 H2.
    exists (fun x => if eq_nat_dec x k then v 
                     else if in_out_interval_dec i1 x then g1 x 
                     else g2 x).
    split; [ | split ].
    + destruct (eq_nat_dec k k) as [ | [] ]; auto.
    + intros x Hx.
      destruct (eq_nat_dec x k) as [ | ].
      * subst; destruct H1; apply interval_union_left; auto.
      * destruct (in_out_interval_dec i1 x) as [ | H3 ]; auto.
        exfalso; revert Hx H3; apply in_out_interval.
    + intros x Hx.
      destruct (eq_nat_dec x k) as [ | ].
      * subst; destruct H1; apply interval_union_right; auto.
      * destruct (in_out_interval_dec i1 x) as [ H3 | ]; auto.
        exfalso; revert H3 Hx; apply H2.
  Qed.

End interval.