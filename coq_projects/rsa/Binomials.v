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
Require Import Wf_nat.
Require Export MiscRsa.
(***********************************************************************
**********************************************************************
**********************************************************************

	ITERATED SUMS
*)

Fixpoint sum_nm (n : nat) : nat -> (nat -> nat) -> nat :=
  fun (m : nat) (f : nat -> nat) =>
  match n with
  | O => f m
  | S n' => f m + sum_nm n' (S m) f
  end.

Lemma sum_nm_i :
 forall (m n : nat) (f : nat -> nat),
 sum_nm (S n) m f = f m + sum_nm n (S m) f.
auto.
Qed.

Lemma sum_nm_f :
 forall (m n : nat) (f : nat -> nat),
 sum_nm (S n) m f = sum_nm n m f + f (m + S n).
intros m n f; generalize m; clear m; elim n; simpl in |- *; intros.
rewrite (plus_comm m); auto.
rewrite H; repeat (rewrite (plus_comm m); simpl in |- *); auto with arith.
Qed.

Lemma sum_nm_ext :
 forall (m n : nat) (f g : nat -> nat),
 (forall x : nat, x <= n -> f (m + x) = g (m + x)) ->
 sum_nm n m f = sum_nm n m g.
Proof.
intros m n f g; generalize m; clear m; elim n; simpl in |- *; intros.
rewrite (plus_n_O m); auto.
rewrite H; auto.
rewrite (plus_n_O m); auto.
rewrite H0; auto with arith.
intros x H'; simpl in |- *; rewrite plus_n_Sm; auto with arith.
Qed.

Lemma sum_nm_add :
 forall (m n : nat) (f g : nat -> nat),
 sum_nm n m f + sum_nm n m g = sum_nm n m (fun i : nat => f i + g i).
Proof.
intros m n f g; generalize m; elim n; auto; intros; simpl in |- *.
rewrite <- H.
repeat rewrite plus_assoc_reverse; apply (f_equal2 (A1:=nat) (A2:=nat)); auto.
repeat rewrite plus_assoc; apply (f_equal2 (A1:=nat) (A2:=nat)); auto.
apply plus_comm.
Qed.

Lemma sum_nm_times :
 forall (m n x : nat) (f : nat -> nat),
 x * sum_nm n m f = sum_nm n m (fun i : nat => x * f i).
Proof.
intros m n x f; generalize m; elim n; auto; intros; simpl in |- *.
rewrite <- H; auto with arith.
repeat rewrite (mult_comm x); auto.
rewrite mult_plus_distr_r; auto.
Qed.

Lemma inv_sum_nm :
 forall (P : nat -> Prop) (i n : nat) (f : nat -> nat),
 (forall a b : nat, P a -> P b -> P (a + b)) ->
 (forall x : nat, x <= n -> P (f (i + x))) -> P (sum_nm n i f).
Proof.
intros P i n f; generalize i; clear i; elim n; clear n; intros; simpl in |- *.
rewrite (plus_n_O i); auto.
apply H0; auto.
rewrite (plus_n_O i); auto with arith.
apply H; auto.
intros x H'; simpl in |- *; rewrite plus_n_Sm; auto with arith.
Qed.

Lemma t_sum_Svars :
 forall (n k : nat) (f : nat -> nat),
 sum_nm k n f = sum_nm k (S n) (fun i : nat => f (pred i)).
Proof.
intros n k f; generalize n; elim k; auto; intros; simpl in |- *.
rewrite <- H; auto.
Qed.
(***********************************************************************
**********************************************************************
**********************************************************************

	BINOMIAL
*)

Fixpoint binomial (a : nat) : nat -> nat :=
  fun b : nat =>
  match a, b with
  | _, O => 1
  | O, S b' => 0
  | S a', S b' => binomial a' (S b') + binomial a' b'
  end.

Lemma binomial_def1 : forall n : nat, binomial n 0 = 1.
Proof.
simple induction n; auto.
Qed.

Lemma binomial_def2 : forall n m : nat, n < m -> binomial n m = 0.
simple induction n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros H'; inversion H'; auto.
intros n0 H' m; case m; simpl in |- *; auto.
intros H'0; inversion H'0; auto.
intros n1 H'0.
rewrite H'; auto with arith.
rewrite H'; auto with arith.
Qed.

Lemma binomial_def3 : forall n : nat, binomial n n = 1.
Proof.
simple induction n; intros; simpl in |- *; auto.
rewrite (binomial_def2 n0 (S n0)); auto.
Qed.

Lemma binomial_def4 :
 forall n k : nat,
 k < n -> binomial (S n) (S k) = binomial n (S k) + binomial n k.
Proof.
simpl in |- *; auto.
Qed.

Lemma binomial_fact :
 forall m n : nat,
 binomial (n + m) n * (factorial n * factorial m) = factorial (n + m).
Proof.
intros m; elim m; clear m.
intros n; rewrite plus_comm; simpl in |- *; rewrite binomial_def3;
 simpl in |- *; rewrite mult_comm; simpl in |- *; rewrite plus_comm;
 simpl in |- *; auto.
intros m H' n; elim n; clear n.
simpl in |- *; rewrite plus_comm; simpl in |- *; rewrite plus_comm;
 simpl in |- *; auto.
intros n H'0.
replace (S n + S m) with (S (S n + m)); [ idtac | simpl in |- * ]; auto.
rewrite binomial_def4;
 [ idtac | rewrite plus_comm; simpl in |- *; rewrite plus_comm ];
 auto with arith.
rewrite mult_plus_distr_r.
apply
 (trans_equal (A:=nat))
  with (y := factorial (S n + m) * S m + factorial (n + S m) * S n).
apply f_equal2 with (A1 := nat) (A2 := nat); auto.
rewrite <- H'.
repeat rewrite mult_assoc_reverse; rewrite (mult_comm (factorial m));
 simpl in |- *; auto.
rewrite <- H'0.
rewrite <- plus_n_Sm; auto.
rewrite mult_assoc_reverse; rewrite mult_comm with (m := S n);
 rewrite (mult_assoc (S n)); simpl in |- *; auto.
apply (trans_equal (A:=nat)) with (y := (S m + S n) * factorial (S n + m)).
rewrite mult_plus_distr_r; apply f_equal2 with (A1 := nat) (A2 := nat).
rewrite (mult_comm (S m)); auto.
rewrite (mult_comm (S n)); rewrite <- plus_n_Sm; auto.
rewrite (plus_comm (S m)); rewrite <- plus_n_Sm; auto.
Qed.

Theorem exp_Pascal :
 forall a b n : nat,
 power (a + b) n =
 sum_nm n 0 (fun k : nat => binomial n k * (power a (n - k) * power b k)).
Proof.
simple induction n; auto.
intros n0; case n0.
simpl in |- *; repeat rewrite mult_comm with (m := 1); simpl in |- *;
 repeat rewrite <- plus_n_O; auto.
intros n1 H'.
apply trans_equal with (y := (a + b) * power (a + b) (S n1)).
simpl in |- *; auto.
rewrite H'; rewrite mult_plus_distr_r; repeat rewrite sum_nm_times.
rewrite sum_nm_i; rewrite binomial_def1.
replace (1 * (power a (S n1 - 0) * power b 0)) with (power a (S n1));
 [ idtac
 | rewrite mult_comm with (m := 1); simpl in |- *;
    repeat rewrite plus_comm with (m := 0) ]; auto.
rewrite sum_nm_f; rewrite binomial_def3.
replace (S n1 - (0 + S n1)) with 0;
 [ idtac | simpl in |- *; apply minus_n_n ]; auto.
replace (power a 0) with 1; auto.
replace (b * (1 * (1 * power b (0 + S n1)))) with (b * power b (S n1));
 [ idtac | simpl in |- *; repeat rewrite <- plus_n_O ]; 
 auto.
rewrite (t_sum_Svars 0 n1).
replace
 (a * power a (S n1) +
  sum_nm n1 1
    (fun z : nat =>
     a * (binomial (S n1) z * (power a (S n1 - z) * power b z))) +
  (sum_nm n1 1
     (fun x : nat =>
      b *
      (binomial (S n1) (pred x) *
       (power a (S n1 - pred x) * power b (pred x)))) + 
   b * power b (S n1))) with
 (power a (S (S n1)) +
  (sum_nm n1 1
     (fun x : nat =>
      binomial (S (S n1)) x * (power a (S (S n1) - x) * power b x)) +
   power b (S (S n1)))).
rewrite (sum_nm_i 0); rewrite (sum_nm_f 1).
rewrite binomial_def1; rewrite binomial_def3.
replace (S (S n1) - 0) with (S (S n1)); auto.
replace (S (S n1) - (1 + S n1)) with 0; auto with arith.
replace (power a 0) with 1; auto.
replace (power b 0) with 1; auto.
replace (1 * (power a (S (S n1)) * 1)) with (power a (S (S n1)));
 [ idtac
 | repeat rewrite mult_comm with (m := 1); simpl in |- *;
    repeat rewrite plus_comm with (m := 0); simpl in |- * ]; 
 auto.
replace (1 + S n1) with (S (S n1)); auto.
replace (1 * (1 * power b (S (S n1)))) with (power b (S (S n1)));
 [ idtac
 | repeat rewrite mult_comm with (m := 1); simpl in |- *;
    rewrite plus_comm with (m := 0); simpl in |- * ]; 
 auto.
repeat rewrite plus_assoc_reverse; apply plus_eq; auto.
repeat rewrite plus_assoc; apply plus_eq; auto.
rewrite sum_nm_add.
apply sum_nm_ext.
intros x H'0.
replace (pred (1 + x)) with x; [ idtac | auto ].
replace (S (S n1) - (1 + x)) with (S n1 - x); [ idtac | auto ].
replace (S n1 - (1 + x)) with (n1 - x); [ idtac | auto ].
replace (1 + x) with (S x); [ idtac | auto ].
rewrite (binomial_def4 (S n1)); auto with arith.
rewrite mult_plus_distr_r.
apply plus_eq.
repeat rewrite mult_assoc; apply mult_eq; auto.
rewrite (mult_comm a); repeat rewrite mult_assoc_reverse; apply mult_eq; auto.
rewrite <- minus_Sn_m; simpl in |- *; auto.
rewrite (mult_comm b); repeat rewrite mult_assoc_reverse; apply mult_eq; auto.
apply mult_eq; auto.
simpl in |- *; apply mult_comm.
Qed.