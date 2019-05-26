(* Ugly tacty to resolve sign condition for N *)
Require Import NatSignTac.
Require Import NAux.
Require Import NArith.
Require Import List.
Require Export NGroundTac.

Open Scope N_scope.

Theorem Nmult_lt_compat_l: forall n m p, n < m -> 0 < p -> p * n < p * m.
intros n m p H1 H2; apply Nlt_lt; repeat rewrite N2Nat.inj_mul.
apply mult_lt_compat_l; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_le_compat_l: forall n m p, n <= m -> p * n <= p * m.
intros n m p H1; apply Nle_le; repeat rewrite N2Nat.inj_mul.
apply Mult.mult_le_compat_l; apply le_Nle; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_ge_compat_l: forall n m p, n >= m -> p * n >= p * m.
intros n m p H1; apply Nge_ge; repeat rewrite N2Nat.inj_mul.
apply mult_ge_compat_l; apply ge_Nge; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_gt_compat_l: forall n m p, n > m -> p > 0 -> p * n > p * m.
intros n m p H1 H2; apply Ngt_gt; repeat rewrite N2Nat.inj_mul.
apply mult_gt_compat_l; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_lt_compat_rev_l1: forall n m p, p * n < p * m -> 0 < p.
intros n m p H1; apply Nlt_lt; apply mult_lt_compat_rev_l1 with (nat_of_N n) (nat_of_N m).
repeat rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_lt_compat_rev_l2: forall n m p, p * n < p * m -> n < m.
intros n m p H1; apply Nlt_lt; apply mult_lt_compat_rev_l2 with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_gt_compat_rev_l1: forall n m p, p * n > p * m -> p > 0.
intros n m p H1; apply Ngt_gt; apply mult_gt_compat_rev_l1 with (nat_of_N n) (nat_of_N m).
repeat rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_gt_compat_rev_l2: forall n m p, p * n > p * m -> n > m.
intros n m p H1; apply Ngt_gt; apply mult_gt_compat_rev_l2 with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_le_compat_rev_l: forall n m p, p * n <= p * m -> 0 < p -> n <= m.
intros n m p H1 H2; apply Nle_le; apply mult_le_compat_rev_l with (nat_of_N p). 
repeat rewrite <- N2Nat.inj_mul; apply le_Nle; repeat rewrite N2Nat.id; auto.
apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_ge_compat_rev_l: forall n m p , p * n >= p * m -> 0 < p -> n >= m.
intros n m p H1 H2; apply Nge_ge; apply mult_ge_compat_rev_l with (nat_of_N p). 
repeat rewrite <- N2Nat.inj_mul; apply ge_Nge; repeat rewrite N2Nat.id; auto.
apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nlt_mult_0: forall a b, 0 < a -> 0 < b -> 0 < a * b.
intros a b H1 H2; apply Nlt_lt; rewrite N2Nat.inj_mul; apply lt_mult_0; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Ngt_mult_0: forall a b, a > 0 -> b > 0 -> a * b > 0.
intros a b H1 H2; apply Ngt_gt; rewrite N2Nat.inj_mul; apply gt_mult_0; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nlt_mult_rev_0_l: forall a b, 0 < a * b ->  0 < a .
intros a b H1; apply Nlt_lt; apply lt_mult_rev_0_l with (nat_of_N b). 
rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nlt_mult_rev_0_r: forall a b, 0 < a * b ->  0 < b .
intros a b H1; apply Nlt_lt; apply lt_mult_rev_0_r with (nat_of_N a). 
rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Ngt_mult_rev_0_l: forall a b, a * b > 0 ->  a > 0.
intros a b H1; apply Ngt_gt; apply gt_mult_rev_0_l with (nat_of_N b). 
rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Ngt_mult_rev_0_r: forall a b, a * b > 0  ->  b > 0 .
intros a b H1; apply Ngt_gt; apply gt_mult_rev_0_r with (nat_of_N a). 
rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nle_0_eq_0: forall n, n <= 0 -> n = 0.
intros n H1; rewrite <- (N2Nat.id n).
rewrite (le_0_eq_0 (nat_of_N n)); auto.
apply le_Nle; rewrite N2Nat.id; auto.
Qed.

Theorem Nge_0_eq_0: forall n, 0 >= n -> n = 0.
intros n H1; rewrite <- (N2Nat.id n).
rewrite (le_0_eq_0 (nat_of_N n)); auto.
change (0 >= nat_of_N n)%nat.
apply ge_Nge; rewrite N2Nat.id; auto.
Qed.

Ltac Nsign_tac :=
 repeat (apply Nmult_le_compat_l || apply Nmult_lt_compat_l ||
              apply Nmult_ge_compat_l || apply Nmult_gt_compat_l ||
              apply Nlt_mult_0 || apply Ngt_mult_0); auto.

Ltac hyp_Nsign_tac H :=
  match type of H with
   0 <= _ => clear H
| (?X1 <= 0)%N => generalize (Nle_0_eq_0 _ H); clear H; intros H; subst X1
|  (?X1 * _ <= ?X1 * _)%N => 
             let s1 := fresh "NS" in
                   (assert (s1: 0 < X1); [Nsign_tac; fail |
                   generalize (Nmult_le_compat_rev_l _ _ _ H s1);
                   clear H s1; intros H])
|   (0  < ?X1 * _)%N  => 
              let s1 := fresh "NS" in
                   (generalize (Nlt_mult_rev_0_l _ _ H);
                    generalize (Nlt_mult_rev_0_r _ _ H); clear H;
                    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H)
|  (?X1 < 0)%N => absurd (~ (X1 < 0)%N); auto
| (?X1 * _  < ?X1 * _)%N => 
              let s1 := fresh "NS" in
                   (generalize (Nmult_lt_compat_rev_l1 _ _ _ H);
                    generalize (Nmult_lt_compat_rev_l2 _ _ _ H); clear H;
                    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H)
|  (?X1 >= 0)%N => clear H
| (0 >= ?X1)%N  => generalize (Nge_0_eq_0 _ H); clear H; intros H; subst X1
|  (?X1 * _ >= ?X1 * _)%N => 
             let s1 := fresh "NS" in
                   (assert (s1: (0 < X1)%N); [Nsign_tac; fail |
                   generalize (Nmult_ge_compat_rev_l _ _ _ H s1);
                   clear H s1; intros H])
|  (?X1 * _ > 0 )%N => 
              let s1 := fresh "NS" in
                   (generalize (Ngt_mult_rev_0_l _ _ H);
                    generalize (Ngt_mult_rev_0_r _ _ H); clear H;
                    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H)
|  (0 > ?X1)%N => absurd (~ (0 > X1)%N); auto with arith
| (?X1 * _  > ?X1 * _)%N => 
              let s1 := fresh "NS" in
                   (generalize (Nmult_gt_compat_rev_l1 _ _ _ H);
                    generalize (Nmult_gt_compat_rev_l2 _ _ _ H); clear H;
                    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H)
  |  _ => (let u := type of H in (clear H; assert (H: u); [auto; fail | clear H]) || idtac)
              
   end.

Close Scope N_scope.