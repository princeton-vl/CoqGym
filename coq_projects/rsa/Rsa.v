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



(****************************************************************
*  Rsa.g                                                      *
****************************************************************)
Require Import Arith.
Require Export Fermat.
Section RSA.
Variable p q : nat.
Variable prime_p : prime p.
Variable prime_q : prime q.
Variable neq_pq : p <> q.
Variable e d : nat.
Variable pq : nat.
Hypothesis pqnot_zero : pq <> 0.
Hypothesis pq_div_p : divides (p - 1) pq.
Hypothesis pq_div_q : divides (q - 1) pq.
Variable ed_inv : congruent pq (e * d) 1.

Definition encrypt (w : nat) : nat := power w e.

Definition decrypt (w : nat) : nat := power w d.

Lemma gcd_pq_SO : is_gcd p q 1.
Proof.
apply prime_gcd; auto.
red in |- *; intros H.
inversion prime_p.
case neq_pq.
apply H1; auto.
inversion prime_q; auto.
Qed.

Lemma Chinese :
 forall a b : nat,
 b <= a -> congruent p a b -> congruent q a b -> congruent (p * q) a b.
Proof.
intros a b H' H'0 H'1.
cut (divides p (a - b)); [ intros H'2; inversion_clear H'2 | idtac ].
cut (divides q (a - b)); [ intros H'3; inversion_clear H'3 | idtac ].
cut (divides p q1); [ intros H'4; inversion_clear H'4 | idtac ].
apply congruentDef with (u := 0) (v := q2); simpl in |- *.
rewrite mult_assoc.
rewrite <- H1; rewrite <- H0; rewrite <- plus_n_O; auto with arith.
apply L_Euclides with q.
apply gcd_pq_SO.
apply dividesDef with (q := q0).
rewrite (mult_comm q); rewrite <- H; auto.
apply cong_divides; auto.
apply cong_divides; auto.
Qed.

Lemma prime_2_or_more : forall r : nat, prime r -> r = 2 \/ 2 < r.
intros r; case r.
intros H'; absurd (prime 0); auto.
intros n; case n.
intros H'; absurd (prime 1); auto.
intros n0; case n0; auto with arith.
Qed.

Lemma phi_gt_SO : 1 < pq.
Proof.
elim (prime_2_or_more p); auto; intros H'1.
elim (prime_2_or_more q); auto; intros H'2.
absurd (p = q); auto.
rewrite H'2; auto.
apply lt_le_trans with (m := q - 1); auto.
apply lt_S_n; simpl in |- *; auto.
replace (S (q - 1)) with (1 + (q - 1)).
rewrite <- (le_plus_minus 1 q); auto.
apply le_trans with (m := 2); auto.
apply lt_le_weak; auto.
simpl in |- *; auto.
apply divides_le; auto.
apply lt_le_trans with (m := p - 1); auto.
apply lt_S_n; simpl in |- *; auto.
replace (S (p - 1)) with (1 + (p - 1)).
rewrite <- (le_plus_minus 1 p); auto.
apply le_trans with (m := 2); auto.
apply lt_le_weak; auto.
simpl in |- *; auto.
apply divides_le; auto.
Qed.

Theorem rsa_correct :
 forall w : nat, congruent (p * q) (decrypt (encrypt w)) w.
Proof.
unfold decrypt, encrypt in |- *.
intros; rewrite power_power.
cut (1 <= e * d); [ intros leH | idtac ].
cut (divides pq (e * d - 1)); [ intros H; inversion_clear H | idtac ].
cut (e * d = 1 + q0 * pq); [ intros Eqed | idtac ].
apply Chinese; auto with arith.
rewrite Eqed; apply power_le; auto with arith.
case (divides_dec p w); intros divPpw.
apply cong_trans with (b := 0).
apply cong_sym.
apply cong_trans with (b := power 0 (e * d)).
rewrite power_O; auto.
apply cong_ref; auto.
apply cong_pow; auto.
apply divides_cong; auto.
apply divides_cong; auto.
rewrite Eqed; simpl in |- *.
inversion_clear pq_div_p.
rewrite mult_comm; apply cong_trans with (b := power 1 (q1 * q0) * w).
apply cong_times; auto.
rewrite mult_comm.
repeat rewrite <- power_power.
apply cong_pow.
rewrite H.
repeat rewrite <- power_power.
rewrite power_SO.
apply Fermat; auto.
red in |- *; intros H'; case divPpw.
apply div_power_prime with (n := q1); auto.
rewrite power_SO; simpl in |- *; rewrite <- plus_n_O; auto.
apply cong_ref; auto.
case (divides_dec q w); intros divPpw.
apply cong_trans with (b := 0).
apply cong_sym.
apply cong_trans with (b := power 0 (e * d)).
rewrite power_O; auto.
apply cong_ref; auto.
apply cong_pow; auto.
apply divides_cong; auto.
apply divides_cong; auto.
rewrite Eqed; simpl in |- *.
inversion_clear pq_div_q.
rewrite mult_comm; apply cong_trans with (b := power 1 (q1 * q0) * w).
apply cong_times; auto.
rewrite mult_comm.
repeat rewrite <- power_power.
apply cong_pow.
rewrite H.
repeat rewrite <- power_power.
rewrite power_SO.
apply Fermat; auto.
red in |- *; intros H'; case divPpw.
apply div_power_prime with (n := q1); auto.
rewrite power_SO; simpl in |- *; rewrite <- plus_n_O; auto.
apply cong_ref; auto.
rewrite <- H0; auto.
rewrite <- le_plus_minus; auto.
apply cong_divides; auto.
apply cong1_le with pq; auto.
apply phi_gt_SO.
Qed.
End RSA.
Section RSAI.
Variable p q : nat.
Variable prime_p : prime p.
Variable prime_q : prime q.
Variable neq_pq : p <> q.
Variable e d : nat.
Variable ed_inv : congruent ((p - 1) * (q - 1)) (e * d) 1.

Theorem rsa_correct' :
 forall w : nat, congruent (p * q) (decrypt d (encrypt e w)) w.
intros w.
apply rsa_correct with (pq := (p - 1) * (q - 1)); auto.
red in |- *; intros H'.
case (mult_eqO _ _ H').
generalize (prime_2_or_more p prime_p); case p; simpl in |- *; auto.
intros H'0; elim H'0; intros H'1; inversion H'1; auto.
intros n; case n; simpl in |- *; auto.
intros H'0; elim H'0; intros H'1; auto.
inversion H'1; auto.
absurd (2 < 1); auto.
apply lt_asym; auto.
intros n0 H'0 H'1; inversion H'1.
generalize (prime_2_or_more q prime_q); case q; simpl in |- *; auto.
intros H'0; elim H'0; intros H'1; inversion H'1; auto.
intros n; case n; simpl in |- *; auto.
intros H'0; elim H'0; intros H'1; auto.
inversion H'1; auto.
absurd (2 < 1); auto.
apply lt_asym; auto.
intros n0 H'0 H'1; inversion H'1.
apply dividesDef with (q := q - 1); auto with arith.
apply dividesDef with (q := p - 1); auto with arith.
Qed.
End RSAI.
