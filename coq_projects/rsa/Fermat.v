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
Require Export Divides.
Require Export Binomials.

Lemma div_fact :
 forall p k : nat,
 prime p ->
 0 < k ->
 divides p (factorial k) -> exists j : nat, 0 < j /\ j <= k /\ divides p j.
Proof.
simple induction k.
simpl in |- *; intros H' H'0; absurd (0 < 0); auto with arith.
intros k' H' H'0 H'1 H'2; case (L_Euclides2 p (S k') (factorial k')); auto.
intros H'3; exists (S k'); auto.
intros H'3.
elim H';
 [ intros j E; elim E; intros H'7 H'8; elim H'8; intros H'9 H'10;
    try exact H'10
 | clear H'
 | clear H'
 | clear H' ]; auto.
exists j; split; auto.
generalize H'3; case k'; simpl in |- *; auto with arith.
intros H'4; absurd (prime 1); auto.
rewrite (divides_antisym 1 p); auto.
Qed.

Lemma p_div_bin :
 forall k p : nat, prime p -> 0 < k -> k < p -> divides p (binomial p k).
Proof.
intros k p; case p; auto.
intros H'; absurd (prime 0); auto.
intros p' H' H'0 H'1.
apply L_Euclides1 with (factorial k); auto.
apply L_Euclides1 with (factorial (S p' - k)); auto.
rewrite mult_assoc.
rewrite mult_comm.
pattern (S p') at 2 in |- *; rewrite (le_plus_minus k (S p'));
 auto with arith.
rewrite mult_comm with (m := factorial k); auto.
rewrite binomial_fact; auto.
rewrite <- le_plus_minus; auto with arith.
apply dividesDef with (q := factorial p'); rewrite mult_comm; auto.
red in |- *; intros H'2; elim (div_fact (S p') (S p' - k));
 [ intros j E; elim E; intros H'7 H'8; elim H'8; intros H'9 H'10; clear H'8 E
 | idtac
 | idtac
 | idtac ]; auto with arith.
absurd (divides (S p') j); auto.
apply not_lt_div; auto.
apply le_lt_trans with (m := S p' - k); auto with arith.
apply lt_minus_O_lt; auto.
red in |- *; intros H'2.
elim (div_fact (S p') k);
 [ intros j E; elim E; intros H'8 H'9; elim H'9; intros H'10 H'11;
    clear H'9 E
 | idtac
 | idtac
 | idtac ]; auto.
absurd (divides (S p') j); auto.
apply not_lt_div; auto.
apply le_lt_trans with (m := k); auto with arith.
Qed.

Lemma Fermat1 :
 forall x p : nat, prime p -> congruent p (power (x + 1) p) (power x p + 1).
Proof.
intros x p; case p; auto.
intros H'; absurd (prime 0); auto.
intros n; case n.
intros H'; absurd (prime 1); auto.
intros n0 H'.
rewrite (exp_Pascal x 1).
rewrite sum_nm_i.
rewrite sum_nm_f.
replace (binomial (S (S n0)) 0 * (power x (S (S n0) - 0) * power 1 0)) with
 (power x (S (S n0))).
replace
 (binomial (S (S n0)) (1 + S n0) *
  (power x (S (S n0) - (1 + S n0)) * power 1 (1 + S n0))) with 1.
rewrite plus_comm with (m := 1).
replace (power x (S (S n0)) + 1) with (power x (S (S n0)) + 1 + 0);
 auto with arith.
rewrite plus_assoc.
apply cong_plus; auto.
apply cong_ref; auto.
apply inv_sum_nm.
replace 0 with (0 + 0); auto.
intros; apply cong_plus; auto.
intros.
apply cong_mult_O.
apply cong_sym.
apply divides_cong.
apply p_div_bin; auto with arith.
simpl in |- *; auto with arith.
simpl in |- *; rewrite binomial_def3; simpl in |- *; auto.
repeat (rewrite binomial_def2; simpl in |- *; auto with arith).
rewrite <- minus_n_n; auto.
rewrite power_SO.
simpl in |- *; auto.
simpl in |- *; auto.
rewrite <- plus_n_O.
rewrite mult_1_r; auto.
Qed.

Lemma Fermat2 : forall x p : nat, prime p -> congruent p (power x p) x.
Proof.
intros x; elim x; auto.
intros p; case p; simpl in |- *; auto.
intros H'; absurd (prime 0); auto.
intros n H'; apply cong_ref; auto.
intros n H' p H'0.
apply (cong_trans p) with (b := power n p + 1).
replace (S n) with (n + 1); auto with arith.
apply Fermat1; auto.
rewrite plus_comm; simpl in |- *; auto.
replace (S n) with (n + 1).
apply cong_plus; auto.
apply cong_ref.
rewrite plus_comm; simpl in |- *; auto.
Qed.

Theorem Fermat :
 forall x p : nat,
 prime p -> ~ divides p x -> congruent p (power x (p - 1)) 1.
Proof.
intros x p H' H'0.
cut (x <= power x p); [ intros Lex | idtac ].
cut (divides p (power x p - x)); [ intros H'1; inversion_clear H'1 | idtac ].
cut (power x p = x * power x (p - 1)); [ intros Eqp | idtac ].
cut (x <> 0); [ intros nx | idtac ].
cut (divides x q); [ intros H2; inversion_clear H2 | idtac ].
apply congruentDef with (u := 0) (v := q0); simpl in |- *; auto.
rewrite <- plus_n_O.
apply eq_mult with x; auto.
rewrite <- Eqp; auto.
rewrite mult_comm; simpl in |- *.
rewrite mult_comm with (m := x).
rewrite mult_assoc.
rewrite (mult_comm x).
rewrite <- H0.
rewrite <- H.
apply le_plus_minus; auto.
apply L_Euclides with (a := p); auto.
apply prime_gcd; auto.
rewrite mult_comm; rewrite <- H.
apply dividesDef with (q := power x (p - 1) - 1); auto.
rewrite mult_minus_distr_r.
apply f_equal2 with (A1 := nat) (A2 := nat); simpl in |- *; auto.
rewrite mult_comm; auto.
red in |- *; intros H'1; case H'0; rewrite H'1; auto.
generalize H'; case p; simpl in |- *; auto with arith.
intros H'1; absurd (prime 0); auto.
apply cong_divides; auto.
apply Fermat2; auto.
generalize H'; case p; auto.
intros H'1; absurd (prime 0); auto.
intros n H'1.
apply power_le; auto with arith.
Qed.
