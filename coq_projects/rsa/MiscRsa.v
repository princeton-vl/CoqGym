(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Import Arith.
Require Export Euclid.
Require Import ZArith.
(***********************************************************************
  **********************************************************************
  **********************************************************************
  Some Arith Facts.*)
 
Theorem lt_mult_right : forall x y z t : nat, x < z -> y < t -> x * y < z * t.
intros x y z t; case x; case z.
intros H'; inversion H'.
simpl in |- *; intros n H'; case t; auto with arith.
intros H'0; inversion H'0.
intros n H'; inversion H'.
intros n n0 H'; case t.
intros H'0; inversion H'0.
intros n1 H'0; apply lt_trans with (m := S n0 * S n1).
apply mult_S_lt_compat_l; auto.
rewrite (mult_comm (S n0)); rewrite (mult_comm (S n)); auto.
apply mult_S_lt_compat_l; auto.
Qed.
 
Theorem le_mult_right : forall x y : nat, 0 < y -> x <= x * y.
intros x y; case y.
intros H'; inversion H'.
intros n H'; rewrite mult_comm; simpl in |- *; auto with arith.
Qed.
(***********************************************************************
  **********************************************************************
  **********************************************************************
  	FACTORIAL*)
 
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.
(***********************************************************************
  **********************************************************************
  **********************************************************************
  	POWER*)
 
Fixpoint power (x n : nat) {struct n} : nat :=
  match n with
  | O => 1
  | S n' => x * power x n'
  end.
 
Lemma power_SO : forall x : nat, power 1 x = 1.
Proof.
simple induction x; auto.
intros; simpl in |- *; rewrite plus_comm; simpl in |- *; auto.
Qed.
 
Lemma power_lt_O : forall x n : nat, 0 < x -> 0 < power x n.
simple induction n; simpl in |- *; auto with arith.
intros n0; case x; intros.
simpl in |- *; auto.
change (0 * 0 < S n1 * power (S n1) n0) in |- *.
apply lt_mult_right; auto.
Qed.
 
Lemma power_le : forall x n : nat, 0 < n -> x <= power x n.
Proof.
intros x n; case n; simpl in |- *; auto.
intros H'; inversion H'.
intros n'; case x; intros; auto.
apply le_mult_right; auto.
apply power_lt_O; auto with arith.
Qed.
 
Lemma power_mult :
 forall x a b : nat, power x a * power x b = power x (a + b).
Proof.
simple induction a; simpl in |- *; auto.
intros n H' b; rewrite mult_assoc_reverse; rewrite H'; auto.
Qed.
 
Lemma power_power : forall x a b : nat, power (power x a) b = power x (a * b).
Proof.
simple induction b; simpl in |- *; auto.
rewrite mult_comm; simpl in |- *; auto.
intros n H'; rewrite mult_comm with (m := S n); simpl in |- *;
 rewrite (mult_comm n); rewrite H'; apply power_mult.
Qed.
 
Lemma SO_power : forall x : nat, power 1 x = 1.
Proof.
simple induction x; simpl in |- *; auto.
intros n H'; rewrite H'; auto.
Qed.
 
Lemma power_O : forall n : nat, 1 <= n -> power 0 n = 0.
Proof.
simple induction n.
intros; absurd (1 <= 0); auto with arith.
intros; simpl in |- *; auto.
Qed.
(**************************************************************************
  *************************************************************************
                                                                         *)
 
Definition plus_eq := f_equal2 plus.
 
Definition mult_eq := f_equal2 mult.
 
Definition minus_eq := f_equal2 minus.
 
Lemma lt_minus_O_lt : forall n m : nat, m < n -> 0 < n - m.
Proof.
intros n m H'.
apply plus_lt_reg_l with (p := m).
rewrite <- le_plus_minus; auto with arith.
rewrite plus_comm; auto.
Qed.
 
Lemma eq_minus : forall a b c : nat, c < a -> a - c = b - c -> a = b.
Proof.
intros a b c H' H'0.
rewrite (le_plus_minus c a); auto with arith.
rewrite (le_plus_minus c b); auto with arith.
apply lt_le_weak.
apply lt_O_minus_lt.
rewrite <- H'0; auto.
apply lt_minus_O_lt; auto.
Qed.
 
Lemma eq_minus' :
 forall a b c : nat, c <= a -> c <= b -> a - c = b - c -> a = b.
Proof.
intros.
rewrite (le_plus_minus c a); auto with arith.
rewrite H1.
rewrite <- le_plus_minus; auto.
Qed.
 
Lemma eq_plus : forall a b c : nat, c + a = c + b -> a = b.
Proof.
intros a b c H'.
apply plus_reg_l with (p := c); auto.
Qed.
 
Lemma plus_eqO : forall x y : nat, x + y = 0 -> x = 0.
Proof.
intros x; case x; simpl in |- *; auto.
intros x' y; case y; simpl in |- *; intros; discriminate.
Qed.
 
Lemma mult_eqO : forall a b : nat, a * b = 0 -> a = 0 \/ b = 0.
Proof.
intros x; case x; simpl in |- *; auto.
intros x' y; case y; simpl in |- *; auto; intros; discriminate.
Qed.
 
Lemma mult_SO : forall x y : nat, x * y = 1 -> x = 1.
Proof.
intros x; case x; simpl in |- *; auto.
intros x' y; case y; simpl in |- *; auto.
rewrite mult_comm; intros; discriminate.
intros n H'; case (mult_eqO x' (S n)).
apply plus_eqO with (y := n).
rewrite plus_comm; apply eq_add_S; auto.
intros H'0; rewrite H'0; auto.
intros; discriminate.
Qed.
 
Lemma mult_eq_Sn : forall a b : nat, 0 < b -> a * b = b -> a = 1.
Proof.
intros a b; case b; simpl in |- *; auto.
intros H; inversion H.
case a; simpl in |- *; auto.
intros; discriminate.
intros b' a' H' H'1; case (mult_eqO b' (S a')); auto.
apply plus_reg_l with (p := S a'); simpl in |- *; rewrite <- plus_n_O; auto.
intros H'0; absurd (0 < S a'); auto; rewrite H'0; auto with arith.
Qed.
(*****************************************************************************)
 
Inductive is_div : nat -> nat -> nat -> nat -> Prop :=
    is_div_def :
      forall a b q r : nat, r < b -> a = q * b + r -> is_div a b q r.
 
Inductive ex_div : nat -> nat -> Prop :=
    ex_div_def : forall a b q r : nat, is_div a b q r -> ex_div a b.
 
Lemma div_x_nO : forall x y q r : nat, is_div x y q r -> y <> 0.
Proof.
intros x y q r; case y; auto.
intros H'; inversion_clear H'.
absurd (0 > r); auto with arith.
Qed.
 
Lemma div_x_O_r : forall x q r : nat, is_div 0 x q r -> r = 0.
Proof.
intros x q r H'; inversion_clear H'.
apply plus_eqO with (y := q * x); rewrite plus_comm; auto with arith.
Qed.
 
Lemma div_x_O_q : forall x q r : nat, is_div 0 x q r -> q = 0.
Proof.
intros x q r H'.
rewrite (div_x_O_r x q r) in H'; inversion H'; auto.
case (mult_eqO q x); auto.
apply plus_eqO with (y := 0); auto.
intros H'1; absurd (x > 0); auto; rewrite H'1; auto with arith.
Qed.
 
Lemma div_pred :
 forall x y q : nat,
 0 < x -> is_div x y q 0 -> is_div (pred x) y (pred q) (pred y).
Proof.
intros x y q H' H'0; inversion_clear H'0.
apply is_div_def; auto with arith.
rewrite H0; auto.
rewrite <- plus_n_O; auto.
generalize H0; case q; simpl in |- *; auto.
intros H'0; absurd (0 < x); auto.
rewrite H'0; auto with arith.
intros n H'0; generalize H; case y; simpl in |- *; auto with arith.
intros H'1; absurd (0 < 0); auto with arith.
Qed.
 
Lemma div_SxS :
 forall x y q r : nat,
 0 < r -> is_div x y q r -> is_div (pred x) y q (pred r).
Proof.
intros x y q r H' H'1; inversion_clear H'1.
apply is_div_def; auto with arith.
generalize H; case r; simpl in |- *; auto with arith.
rewrite H0; generalize H'; case r; simpl in |- *; auto.
intros H'1; absurd (0 < 0); auto with arith.
intros r'; rewrite <- plus_n_Sm; auto.
Qed.
 
Lemma div_unic_r :
 forall a b q1 q2 r1 r2 : nat,
 is_div a b q1 r1 -> is_div a b q2 r2 -> r1 = r2.
intros a; elim a; auto.
intros b q1 q2 r1 r2 H' H'0.
apply trans_eq with (y := 0); auto.
apply div_x_O_r with (x := b) (q := q1); auto.
apply sym_eq; apply div_x_O_r with (x := b) (q := q2); auto.
intros n H' b q1 q2 r1 r2; case r1; case r2; auto.
intros n0 H'0 H'1; inversion_clear H'0; inversion_clear H'1.
cut (S n0 = (q1 - q2) * b); [ intros EqSn0 | idtac ].
generalize H1; rewrite EqSn0; case (q1 - q2); auto with arith.
intros n1 H'0; absurd (b > S n1 * b); auto; simpl in |- *; auto with arith.
rewrite mult_minus_distr_r; apply plus_minus.
rewrite (plus_n_O (q1 * b)); rewrite <- H0; auto.
intros n0 H'0 H'1; inversion_clear H'0; inversion_clear H'1.
cut (S n0 = (q2 - q1) * b); [ intros EqSn0 | idtac ].
generalize H; rewrite EqSn0; case (q2 - q1); auto with arith.
intros n1 H'0; absurd (b > S n1 * b); auto; simpl in |- *; auto with arith.
rewrite mult_minus_distr_r; apply plus_minus.
rewrite (plus_n_O (q2 * b)); rewrite <- H0; auto.
intros n0 n1 H'0 H'1; rewrite (H' b q1 q2 n1 n0); auto.
apply (div_SxS (S n) b q1 (S n1)); auto with arith.
apply (div_SxS (S n) b q2 (S n0)); auto with arith.
Qed.
 
Theorem simpl_mult_r : forall n m p : nat, 0 < n -> m * n = p * n -> m = p.
intros n m; elim m; simpl in |- *; auto.
intros p H' H'0; case (mult_eqO p n); auto.
intros H'1; absurd (0 < n); auto; rewrite H'1; auto with arith.
intros m' H' p; case p; simpl in |- *; auto.
case n; simpl in |- *; intros; try discriminate; absurd (0 < 0);
 auto with arith.
intros p' H'0 H'1.
rewrite (H' p'); auto.
apply plus_reg_l with (p := n); auto.
Qed.
 
Lemma div_unic_q :
 forall a b q1 q2 r1 r2 : nat,
 is_div a b q1 r1 -> is_div a b q2 r2 -> q1 = q2.
Proof.
intros a b; case b; auto.
intros q1 q2 r1 r2 H' H'0; inversion_clear H'0; inversion_clear H'.
inversion H1; auto.
intros b' q1 q2 r1 r2 H' H'0.
rewrite (div_unic_r a (S b') q1 q2 r1 r2) in H'; auto.
inversion_clear H'0; inversion_clear H'.
apply simpl_mult_r with (n := S b'); auto with arith.
apply plus_reg_l with (p := r2).
repeat rewrite (plus_comm r2); rewrite <- H2; auto.
Qed.
 
Lemma quot_eq :
 forall a b c q1 r1 q2 r2 : nat,
 a = b -> is_div a c q1 r1 -> is_div b c q2 r2 -> q1 = q2.
Proof.
intros.
rewrite H in H0.
apply div_unic_q with (1 := H0) (2 := H1); auto.
Qed.
 
Lemma mult_div_r : forall x y q r : nat, is_div (x * y) y q r -> r = 0.
intros x y q r H'.
apply div_unic_r with (a := x * y) (b := y) (q1 := q) (q2 := x);
 auto with arith.
apply is_div_def; inversion_clear H'; auto with arith.
apply le_lt_trans with (m := r); auto with arith.
Qed.
 
Lemma mult_div_q : forall x y q r : nat, is_div (x * y) y q r -> q = x.
Proof.
intros x y q r H'.
apply div_unic_q with (a := x * y) (b := y) (r1 := r) (r2 := 0); auto.
apply is_div_def; inversion_clear H'; auto with arith.
apply le_lt_trans with (m := r); auto with arith.
Qed.
 
Lemma diveucl_divex :
 forall a b : nat,
 diveucl a b -> exists q : _, (exists r : _, is_div a b q r).
Proof.
intros.
elim H.
intros q r H' H'0; exists q; exists r; split; auto.
Qed.
 
Lemma div_ex :
 forall a b : nat, b <> 0 -> exists q : _, (exists r : _, is_div a b q r).
Proof.
intros.
apply diveucl_divex.
apply eucl_dev.
generalize H; case b; auto with arith.
Qed.
 
Lemma eq_mult : forall a b c : nat, c <> 0 -> c * a = c * b -> a = b.
Proof.
intros a b c; case c; auto.
intros H'; case H'; auto.
intros n H' H'0; apply simpl_mult_r with (n := S n);
 repeat rewrite mult_comm with (m := S n); auto with arith.
Qed.
 
Lemma le_plus_le : forall a b c d : nat, a <= b -> a + c = b + d -> d <= c.
Proof.
intros.
cut (c = b - a + d).
intros H1; rewrite H1.
auto with arith.
apply plus_reg_l with (p := a); auto.
rewrite plus_assoc.
rewrite le_plus_minus_r; auto.
Qed.
 
Lemma plus_minus_assoc : forall a b c : nat, b <= a -> a - b + c = a + c - b.
Proof.
simple induction c.
repeat rewrite plus_comm with (m := 0); simpl in |- *; auto.
intros.
rewrite plus_comm; simpl in |- *; rewrite plus_comm.
rewrite H; auto.
rewrite <- plus_Snm_nSm.
rewrite minus_Sn_m; auto with arith.
Qed.