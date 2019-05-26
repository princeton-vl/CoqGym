(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Binomial theorem *)

Require Import Arith Omega.

Require Import utils_tac gcd.

Set Implicit Arguments.

Section factorial.

  Fixpoint fact n := match n with 0 => 1 | S n => (S n) * fact n end.

  Fact fact_0 : fact 0 = 1.
  Proof. trivial. Qed.

  Fact fact_S n : fact (S n) = (S n)*fact n.
  Proof. trivial. Qed.

  Fact fact_gt_0 n : 0 < fact n.
  Proof.
    unfold lt; simpl.
    induction n as [ | n IHn ]; simpl; auto.
    generalize (n*fact n); intros; omega.
  Qed.

End factorial.

Section binomial.

  Infix "<d" := divides (at level 70, no associativity).

  Hint Resolve divides_refl.

  Let fact_neq_0 n : fact n <> 0.
  Proof. generalize (fact_gt_0 n); omega. Qed.

  Fixpoint binomial n p :=
    match n, p with
      | n, 0     => 1
      | 0, S _   => 0
      | S n, S p => binomial n p + binomial n (S p)
    end.

  Fact binomial_n0 n : binomial n 0 = 1.
  Proof. destruct n; auto. Qed.

  Fact binomial_SS n p : binomial (S n) (S p) = binomial n p + binomial n (S p).
  Proof. auto. Qed.

  Fact binomial_n1 n : 1 <= n -> binomial n 1 = n.
  Proof.
    destruct n as [ | n ]; try omega; intros _.
    induction n as [ | n IHn ]; auto.
    rewrite binomial_SS, IHn, binomial_n0; omega.
  Qed.

  Fact binomial_gt n : forall p, n < p -> binomial n p = 0.
  Proof.
    induction n as [ | n IHn ]; intros [|] ?; simpl; auto; try omega.
    do 2 (rewrite IHn; try omega).
  Qed.

  Fact binomial_nn n : binomial n n = 1.
  Proof.
    induction n; auto; rewrite binomial_SS, binomial_gt with (p := S _); omega.
  Qed.

  Theorem binomial_thm n p : p <= n -> fact n = binomial n p * fact p * fact (n-p).
  Proof.
    intros H.
    replace n with (n-p+p) at 1 2 by omega.
    generalize (n-p); clear n H; intros n.
    induction on n p as IH with measure (n+p).
    revert n p IH; intros [ | n ] [ | p ] IH; simpl plus; auto.
    + rewrite binomial_nn; simpl; omega.
    + rewrite Nat.add_0_r, binomial_n0; simpl; omega.
    + rewrite fact_S, binomial_SS.
      replace (S (n+S p)) with (S p+S n) by omega.
      do 3 rewrite Nat.mul_add_distr_r; f_equal.
      * replace (n+S p) with (S n+p) by omega.
        rewrite fact_S, IH; try omega; ring.
      * rewrite (fact_S n), IH; try omega; ring.
  Qed.

  Fact binomial_le n p : p <= n -> binomial n p = div (fact n) (fact p * fact (n-p)).
  Proof.
    intros H.
    symmetry; apply div_prop with (r := 0).
    + rewrite binomial_thm with (p := p); auto; ring.
    + red; change 1 with (1*1); apply mult_le_compat; apply fact_gt_0.
  Qed.

  Fact binomial_sym n p : p <= n -> binomial n p = binomial n (n-p).
  Proof.
    intros H; do 2 (rewrite binomial_le; try omega).
    rewrite mult_comm; do 3 f_equal; omega.
  Qed.

  Fact binomial_spec n p : p <= n -> fact n = binomial n p * fact p * fact (n-p).
  Proof. apply binomial_thm. Qed.

  Fact binomial_0n n : 0 < n -> binomial 0 n = 0.
  Proof. intros; rewrite binomial_gt; auto; simpl. Qed.

  Theorem binomial_pascal n p : binomial (S n) (S p) = binomial n p + binomial n (S p).
  Proof. auto. Qed.

End binomial.
