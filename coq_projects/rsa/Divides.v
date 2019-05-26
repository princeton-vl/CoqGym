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
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
Require Export MiscRsa.
(******************************************************************************)
 
Inductive divides : nat -> nat -> Prop :=
    dividesDef : forall a b q : nat, b = q * a -> divides a b.
 
Lemma div_ref : forall a : nat, divides a a.
intros a; apply dividesDef with (q := 1); auto with arith.
Qed.
 
Lemma div_divides :
 forall x y : nat, (exists q : _, is_div x y q 0) -> divides y x.
Proof.
intros x y H'; elim H'; intros q E; inversion_clear E; clear H'.
apply dividesDef with (q := q); auto.
rewrite H0; auto with arith.
Qed.
 
Lemma divides_div :
 forall x y : nat, 0 < y -> divides y x -> exists q : _, is_div x y q 0.
Proof.
intros x y H'1 H'2; inversion H'2.
exists q; auto.
apply is_div_def; auto with arith.
rewrite H; auto.
Qed.
 
Lemma divides_dec' :
 forall x y : nat,
 {(exists q : _, is_div x y q 0)} + {~ (exists q : _, is_div x y q 0)}.
Proof.
intros x y; case y; auto.
right; red in |- *; intros H'; elim H'; intros q E; inversion E; clear H';
 auto.
inversion H.
intros y'; case (eucl_dev (S y') (gt_Sn_O y') x).
intros q r; case r; auto.
intros H' H'0; left; exists q; auto.
apply is_div_def; auto; rewrite H'0; auto with arith.
intros n H' H'0; right; red in |- *; intros H'1; elim H'1; intros q0 E;
 clear H'1.
absurd (0 = S n); auto with arith.
apply div_unic_r with (a := x) (b := S y') (q1 := q0) (q2 := q); auto.
apply is_div_def; auto with arith.
Qed.
 
Lemma divides_dec : forall x y : nat, {divides x y} + {~ divides x y}.
intros x y; case x; case y; auto.
left; apply dividesDef with (q := 0); auto.
intros n; right; red in |- *; intros H'; inversion_clear H'.
rewrite (mult_comm q 0) in H; discriminate.
intros n; left; apply dividesDef with (q := 0); auto.
intros x' y'; case (divides_dec' (S x') (S y')); auto.
intros H'; left; apply div_divides; auto.
intros H'; right; red in |- *; intros H'0; case H'; auto.
inversion H'0.
exists q; auto.
apply is_div_def; auto with arith.
rewrite H; auto with arith.
Qed.
 
Lemma all_divides_O : forall n : nat, divides n 0.
Proof.
intros n; apply dividesDef with (q := 0); auto.
Qed.
 
Lemma SO_divides_all : forall n : nat, divides 1 n.
Proof.
intros n; apply dividesDef with (q := n); auto with arith.
Qed.
 
Lemma divides_plus1 :
 forall a b c : nat, divides a b -> divides a c -> divides a (b + c).
Proof.
intros a b c H' H'0; inversion_clear H'; inversion_clear H'0.
apply dividesDef with (q := q + q0); auto.
rewrite H; rewrite H0; auto with arith.
Qed.
 
Lemma divides_plus2 :
 forall a b c : nat, divides a b -> divides a (b + c) -> divides a c.
Proof.
intros a b c H' H'0; inversion_clear H'; inversion_clear H'0.
apply dividesDef with (q := q0 - q).
rewrite mult_minus_distr_r.
rewrite <- H; rewrite <- H0.
rewrite minus_plus; auto.
Qed.
 
Theorem divides_le : forall a b : nat, b <> 0 -> divides a b -> a <= b.
intros a b; case b.
intros H'; case H'; auto.
intros n H' H'0; inversion_clear H'0.
rewrite H; generalize H; case q; simpl in |- *; auto with arith; intros;
 discriminate.
Qed.
 
Lemma divides_antisym : forall a b : nat, divides a b -> divides b a -> a = b.
Proof.
intros a b; case a; case b; auto.
intros b' H' H'1; inversion_clear H'.
rewrite H; auto with arith.
intros a' H' H'1; inversion_clear H'1.
rewrite H; auto with arith.
intros n n0 H' H'0; apply le_antisym; apply divides_le; auto.
Qed.
 
Lemma not_lt_div : forall a b : nat, 0 < b -> b < a -> ~ divides a b.
intros a b H'1 H'2; red in |- *; intros H'3; absurd (a <= b); auto with arith.
apply divides_le; auto.
apply sym_not_eq; auto with arith.
Qed.
(********************************************************************)
 
Inductive prime : nat -> Prop :=
    primeDef :
      forall a : nat,
      a <> 1 -> (forall b : nat, divides b a -> b <> 1 -> a = b) -> prime a.
 
Lemma not_prime_O : ~ prime 0.
Proof.
red in |- *; intros H'; inversion_clear H'; auto.
absurd (0 = 2); auto with arith.
apply H0; auto.
apply all_divides_O.
Qed.
 
Lemma not_prime_1 : ~ prime 1.
Proof.
red in |- *; intros H'; inversion_clear H'; auto.
Qed.
Hint Resolve div_ref all_divides_O SO_divides_all not_prime_O not_prime_1.
 
Lemma lt_prime : forall p : nat, prime p -> 1 < p.
Proof.
intros p; case p.
intro; absurd (prime 0); auto.
intros n; case n.
intro; absurd (prime 1); auto.
intros; auto with arith.
Qed.
(**********************************************************************)
 
Inductive is_gcd (a b c : nat) : Prop :=
    is_gcd_intro :
      divides c a ->
      divides c b ->
      (forall d : nat, divides d a -> divides d b -> divides d c) ->
      is_gcd a b c.
 
Lemma is_gcd_unic :
 forall a b c d : nat, is_gcd a b c -> is_gcd a b d -> c = d.
Proof.
intros a b c d H' H'0; inversion_clear H'; inversion_clear H'0.
apply divides_antisym; auto.
Qed.
 
Lemma is_gcd_ref : forall x : nat, is_gcd x x x.
Proof.
intros x; apply is_gcd_intro; auto.
Qed.
 
Lemma is_gcd_sym : forall a b c : nat, is_gcd a b c -> is_gcd b a c.
intros a b c H; inversion_clear H; intros.
apply is_gcd_intro; auto.
Qed.
 
Lemma is_gcd_O' : forall a r : nat, is_gcd a 0 r -> a = r.
Proof.
intros a r H'; inversion_clear H'.
apply divides_antisym; auto.
Qed.
 
Lemma is_gcd_Ol : forall a : nat, is_gcd a 0 a.
intros a.
apply is_gcd_intro; auto.
Qed.
 
Lemma is_gcd_Or : forall a : nat, is_gcd 0 a a.
intros a.
apply is_gcd_intro; auto.
Qed.
 
Lemma prime_gcd : forall p n : nat, prime p -> ~ divides p n -> is_gcd n p 1.
intros p n H' H'0.
apply is_gcd_intro; auto.
intros d H'1 H'2.
inversion_clear H'.
elim (eq_nat_dec d 1); intros H'4; auto.
rewrite H'4; auto.
elim (eq_nat_dec p d); intros H'5; auto.
case H'0; try rewrite H'5; auto.
case H'5; apply H0; auto.
Qed.
 
Lemma gcd_rec :
 forall P : nat -> nat -> Set,
 (forall x : nat, P 0 x) ->
 (forall x : nat, P x 0) ->
 (forall a b : nat, P a b -> P a (b + a)) ->
 (forall a b : nat, P a b -> P (a + b) b) -> forall a b : nat, P a b.
Proof.
intros P H H0 H1 H2 a; pattern a in |- *; apply lt_wf_rec.
intros a' H' b; pattern b in |- *; apply lt_wf_rec.
intros b' H'0.
case (lt_eq_lt_dec a' b'); intros Ca'b';
 [ case Ca'b'; clear Ca'b'; intros Ca'b' | idtac ].
2: rewrite Ca'b'; auto.
2: pattern b' at 1 in |- *; replace b' with (0 + b'); auto.
replace b' with (b' - a' + a'); auto with arith.
case (zerop a'); intros lta'.
rewrite lta'; auto.
apply H1; apply H'0; auto with arith.
rewrite plus_comm; auto with arith.
replace a' with (a' - b' + b'); auto with arith.
case (zerop b'); intros ltb'.
rewrite ltb'; auto.
apply H2; apply H'; auto with arith.
rewrite plus_comm; auto with arith.
Qed.
 
Lemma gcd_ind :
 forall P : nat -> nat -> Prop,
 (forall x : nat, P 0 x) ->
 (forall x : nat, P x 0) ->
 (forall a b : nat, P a b -> P a (b + a)) ->
 (forall a b : nat, P a b -> P (a + b) b) -> forall a b : nat, P a b.
Proof.
intros P H H0 H1 H2 a; pattern a in |- *; apply lt_wf_ind.
intros a' H' b; pattern b in |- *; apply lt_wf_ind.
intros b' H'0.
case (lt_eq_lt_dec a' b'); intros Ca'b';
 [ case Ca'b'; clear Ca'b'; intros Ca'b' | idtac ].
2: rewrite Ca'b'; auto.
2: pattern b' at 1 in |- *; replace b' with (0 + b'); auto.
replace b' with (b' - a' + a'); auto with arith.
case (zerop a'); intros lta'.
rewrite lta'; auto.
apply H1; apply H'0; auto with arith.
rewrite plus_comm; auto with arith.
replace a' with (a' - b' + b'); auto with arith.
case (zerop b'); intros ltb'.
rewrite ltb'; auto.
apply H2; apply H'; auto with arith.
rewrite plus_comm; auto with arith.
Qed.
 
Inductive gcd_spec : nat -> nat -> nat -> Prop :=
  | gcd_spec_ex0 : forall a : nat, gcd_spec a 0 a
  | gcd_spec_ex1 : forall b : nat, gcd_spec 0 b b
  | gcd_spec_ex2 :
      forall a b c : nat, a < b -> gcd_spec a (b - a) c -> gcd_spec a b c
  | gcd_spec_ex3 :
      forall a b c : nat, b <= a -> gcd_spec (a - b) b c -> gcd_spec a b c.
Hint Resolve gcd_spec_ex0 gcd_spec_ex1.
 
Theorem gcd_inv_Or_aux : forall a b c : nat, gcd_spec a b c -> b = 0 -> a = c.
intros a b c H'; elim H'; auto.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
apply H'2; auto.
rewrite H'3; auto.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
replace a0 with (a0 - b0); auto.
rewrite H'3; auto with arith.
Qed.
 
Theorem gcd_inv_Or : forall a b : nat, gcd_spec a 0 b -> a = b.
intros a b H'.
apply gcd_inv_Or_aux with (b := 0); auto.
Qed.
 
Theorem gcd_inv_Ol_aux : forall a b c : nat, gcd_spec a b c -> a = 0 -> b = c.
intros a b c H'; elim H'; auto.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
replace b0 with (b0 - a0); auto.
rewrite H'3; auto with arith.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
apply H'2; auto.
rewrite H'3; auto.
Qed.
 
Theorem gcd_inv_Ol : forall a b : nat, gcd_spec 0 a b -> a = b.
intros a b H'.
apply gcd_inv_Ol_aux with (a := 0); auto.
Qed.
 
Definition gcd' :=
  gcd_rec (fun _ _ : nat => nat) (fun x : nat => x) 
    (fun x : nat => x) (fun x y r : nat => r) (fun x y r : nat => r).
 
Lemma gcd_ex : forall a b : nat, {r : nat | gcd_spec a b r}.
intros a b; pattern b, a in |- *; apply gcd_rec; clear a b.
intros a; exists a; auto.
intros b; exists b; auto.
intros a b Rr; case Rr; intros r Hr; exists r.
apply gcd_spec_ex3; auto with arith.
rewrite plus_comm; rewrite minus_plus; auto; rewrite <- minus_n_n; auto.
intros a b Rr; case Rr; intros r Hr; exists r.
case (zerop a); intros lta.
rewrite lta; simpl in |- *.
rewrite <- (gcd_inv_Or b r); auto.
apply gcd_spec_ex3; auto with arith.
rewrite <- minus_n_n; auto.
rewrite <- lta; auto.
apply gcd_spec_ex2; auto with arith.
pattern b at 1 in |- *; replace b with (0 + b); auto with arith.
rewrite plus_comm; rewrite minus_plus; auto; rewrite <- minus_n_n; auto.
Qed.
 
Definition gcd (a b : nat) := proj1_sig (gcd_ex a b).
 
Lemma gcd_correct : forall a b : nat, gcd_spec a b (gcd a b).
Proof.
intros a b; unfold gcd in |- *; case (gcd_ex a b); simpl in |- *; auto.
Qed.
Hint Resolve gcd_correct.
 
Lemma gcd_spec_uniq :
 forall a b r1 r2 : nat, gcd_spec a b r1 -> gcd_spec a b r2 -> r1 = r2.
intros a b r1 r2 H'; generalize r2; elim H'; clear H' a b r1 r2.
exact gcd_inv_Or.
exact gcd_inv_Ol.
intros a b c H' H'0 H'1 r2 H'2; inversion H'2; auto.
apply H'1; auto.
rewrite <- H0; simpl in |- *; rewrite H1; auto.
apply H'1; auto.
rewrite <- H; simpl in |- *; rewrite <- minus_n_O; rewrite H1; auto.
absurd (a < b); auto with arith.
intros a b c H' H'0 H'1 r2 H'2; inversion H'2; auto.
apply H'1; auto.
rewrite <- H0; simpl in |- *; rewrite H1; rewrite <- minus_n_O; auto.
apply H'1; auto.
rewrite <- H; simpl in |- *; rewrite H1; auto.
absurd (a < b); auto with arith.
Qed.
 
Lemma gcd_correct2 : forall a b r : nat, gcd_spec a b r -> gcd a b = r.
Proof.
intros a b r H'.
apply gcd_spec_uniq with (a := a) (b := b); auto.
Qed.
 
Lemma gcd_def0l : forall x : nat, gcd 0 x = x.
Proof.
intros x; apply gcd_spec_uniq with (a := 0) (b := x); auto.
Qed.
 
Lemma gcd_def0r : forall x : nat, gcd x 0 = x.
Proof.
intros x; apply gcd_spec_uniq with (a := x) (b := 0); auto.
Qed.
 
Lemma gcd_def1 : forall x : nat, gcd x x = x.
Proof.
intros x; apply gcd_spec_uniq with (a := x) (b := x); auto.
apply gcd_spec_ex3; auto.
rewrite <- minus_n_n; auto.
Qed.
 
Lemma gcd_def2 : forall a b : nat, gcd a b = gcd a (b + a).
Proof.
intros a b; apply gcd_spec_uniq with (a := a) (b := b + a); auto.
case (zerop b); intros ltb.
rewrite ltb; simpl in |- *; rewrite gcd_def0r; auto.
apply gcd_spec_ex3; auto.
rewrite <- minus_n_n; auto.
apply gcd_spec_ex2; auto with arith.
replace a with (0 + a); auto with arith.
rewrite plus_comm; rewrite minus_plus.
apply gcd_correct; auto.
Qed.
 
Lemma gcd_def3 : forall a b : nat, gcd a b = gcd (a + b) b.
Proof.
intros a b; apply gcd_spec_uniq with (a := a + b) (b := b); auto.
case (zerop a); intros lta.
rewrite lta; simpl in |- *; rewrite gcd_def0l; auto.
apply gcd_spec_ex3; auto with arith.
rewrite <- minus_n_n; auto.
apply gcd_spec_ex3; auto with arith.
rewrite plus_comm; rewrite minus_plus.
apply gcd_correct; auto.
Qed.
 
Lemma gcd_is_gcd : forall a b : nat, is_gcd a b (gcd a b).
Proof.
intros; pattern a, b in |- *; apply gcd_ind; clear a b.
intros x; rewrite gcd_def0l; auto.
apply is_gcd_Or; auto.
intros x; rewrite gcd_def0r; auto.
apply is_gcd_Ol; auto.
intros a b H'; rewrite <- gcd_def2.
inversion_clear H'.
apply is_gcd_intro; auto.
apply divides_plus1; auto.
intros d H' H'0.
apply H1; auto.
apply divides_plus2 with (b := a); auto.
rewrite plus_comm; auto.
intros a b H'; rewrite <- gcd_def3.
inversion_clear H'.
apply is_gcd_intro; auto.
apply divides_plus1; auto.
intros d H' H'0.
apply H1; auto.
apply divides_plus2 with (b := b); auto.
rewrite plus_comm; auto.
Qed.
 
Lemma preEuclid :
 forall a b c m : nat,
 divides c (m * a) -> divides c (m * b) -> divides c (m * gcd a b).
Proof.
intros a b; pattern a, b in |- *; apply gcd_ind; clear a b.
intros x c m H' H'0; rewrite gcd_def0l; auto.
intros x c m H' H'0; rewrite gcd_def0r; auto.
intros a b H' c m H'0 H'1; rewrite <- gcd_def2.
apply H'; auto.
apply divides_plus2 with (m * a); auto.
rewrite mult_comm; pattern mult at 1 in |- *; rewrite mult_comm;
 rewrite <- mult_plus_distr_r; rewrite mult_comm.
rewrite plus_comm; simpl in |- *; assumption.
intros a b H' c m H'0 H'1; rewrite <- gcd_def3.
apply H'; auto.
apply divides_plus2 with (m * b); auto.
rewrite mult_comm; pattern mult at 1 in |- *; rewrite mult_comm;
 rewrite <- mult_plus_distr_r; rewrite mult_comm.
rewrite plus_comm; simpl in |- *; assumption.
Qed.
 
Theorem L_Euclides :
 forall x a b : nat, is_gcd x a 1 -> divides x (a * b) -> divides x b.
Proof.
intros x a b H' H'0; replace b with (b * gcd x a).
apply preEuclid; auto with arith.
apply dividesDef with (q := b); auto with arith.
rewrite mult_comm; auto.
rewrite (is_gcd_unic x a (gcd x a) 1); auto with arith.
apply gcd_is_gcd; auto.
Qed.
 
Lemma L_Euclides1 :
 forall p a b : nat,
 prime p -> divides p (a * b) -> ~ divides p a -> divides p b.
intros; apply L_Euclides with a; auto.
apply is_gcd_sym.
apply prime_gcd; auto.
Qed.
 
Lemma L_Euclides2 :
 forall p a b : nat,
 prime p -> divides p (a * b) -> divides p a \/ divides p b.
intros.
elim (divides_dec p a); [ left | right ]; auto.
apply L_Euclides1 with a; auto.
Qed.
 
Theorem div_power_prime :
 forall p w n : nat, prime p -> divides p (power w n) -> divides p w.
intros p w n; elim n; simpl in |- *; auto.
intros H' H'0; inversion_clear H'0.
generalize H' H; case q; case p; simpl in |- *; intros; try discriminate.
absurd (prime 0); auto.
generalize H0; case n0; simpl in |- *; auto.
intros n2 H'1; absurd (1 = S (S (n2 + n1 * S (S n2)))); auto.
intros n0 H' H'0 H'1.
case (divides_dec p (power w n0)); intros H; auto.
apply L_Euclides1 with (a := power w n0); auto.
rewrite mult_comm; auto.
Qed.
Section CD.
Variable n : nat.
(**********************************************************************)
 
Inductive congruent : nat -> nat -> Prop :=
    congruentDef :
      forall a b u v : nat, a + u * n = b + v * n -> congruent a b.
 
Lemma cong_ref : forall a : nat, congruent a a.
Proof.
intros a.
apply congruentDef with (u := 1) (v := 1); auto.
Qed.
 
Lemma cong_sym : forall a b : nat, congruent a b -> congruent b a.
Proof.
intros a b H; elim H.
intros a0 b0 c d H'.
apply congruentDef with (u := d) (v := c); auto.
Qed.
 
Lemma cong_trans :
 forall a b c : nat, congruent a b -> congruent b c -> congruent a c.
Proof.
intros a b c H' H'0; inversion_clear H'; inversion_clear H'0.
apply congruentDef with (u := u + u0) (v := v + v0); auto.
repeat rewrite mult_plus_distr_r; repeat rewrite plus_assoc; rewrite H.
repeat rewrite plus_comm with (m := v * n); repeat rewrite plus_assoc_reverse;
 rewrite H0; auto.
Qed.
 
Lemma cong_mult_O : forall a b : nat, congruent a 0 -> congruent (a * b) 0.
Proof.
intros a b H'; inversion_clear H'.
apply congruentDef with (u := u * b) (v := v * b).
repeat rewrite mult_comm with (m := b); repeat rewrite mult_assoc_reverse;
 repeat rewrite (mult_comm b).
rewrite <- mult_plus_distr_r; rewrite H; rewrite mult_plus_distr_r;
 simpl in |- *; auto.
Qed.
 
Lemma cong_plus :
 forall a b c d : nat,
 congruent a b -> congruent c d -> congruent (a + c) (b + d).
Proof.
intros a b c d H' H'0; inversion_clear H'; inversion_clear H'0.
apply congruentDef with (u := u0 + u) (v := v0 + v).
repeat rewrite mult_plus_distr_r; repeat rewrite plus_assoc_reverse.
rewrite (plus_assoc c); rewrite (plus_assoc d); rewrite H0.
rewrite (plus_comm a); rewrite (plus_comm b);
 repeat rewrite plus_assoc_reverse; rewrite plus_comm with (m := a);
 rewrite plus_comm with (m := b); rewrite H; auto.
Qed.
 
Lemma cong_add :
 forall a b c : nat, congruent a b -> congruent (a + c) (b + c).
Proof.
intros a b c H; inversion_clear H.
apply congruentDef with (u := u) (v := v); auto.
repeat rewrite plus_comm with (m := c); repeat rewrite plus_assoc_reverse;
 rewrite H0; auto.
Qed.
 
Lemma cong_times :
 forall a b c : nat, congruent a b -> congruent (a * c) (b * c).
intros a b c H; inversion_clear H.
apply congruentDef with (u := u * c) (v := v * c); auto.
repeat rewrite mult_comm with (m := c); repeat rewrite mult_assoc_reverse;
 repeat rewrite (mult_comm c).
repeat rewrite <- mult_plus_distr_r.
rewrite H0; auto.
Qed.
 
Lemma cong_mult :
 forall a b c d : nat,
 congruent a b -> congruent c d -> congruent (a * c) (b * d).
intros a b c d H' H'0; inversion_clear H'; inversion_clear H'0.
apply
 congruentDef
  with (u := u0 * a + u * u0 * n + u * c) (v := v0 * b + v * v0 * n + v * d).
repeat rewrite mult_plus_distr_r.
repeat rewrite plus_assoc.
rewrite (mult_comm u0); rewrite (mult_comm v0).
repeat rewrite mult_assoc_reverse.
repeat rewrite (mult_comm a); repeat rewrite (mult_comm b).
repeat rewrite <- mult_plus_distr_r.
repeat rewrite mult_assoc.
repeat rewrite mult_comm with (m := n).
rewrite (mult_assoc n u); rewrite (mult_assoc n v).
repeat rewrite mult_assoc.
repeat rewrite (mult_assoc_reverse n n).
rewrite mult_comm with (m := n * u); rewrite mult_comm with (m := n * v).
repeat rewrite mult_assoc_reverse with (m := n).
repeat rewrite (mult_comm (n * u)); repeat rewrite (mult_comm (n * v)).
repeat rewrite plus_assoc_reverse; repeat rewrite <- mult_plus_distr_r.
rewrite plus_comm with (m := c); rewrite plus_comm with (m := d).
repeat rewrite (mult_comm (c + n * u0));
 repeat rewrite (mult_comm (d + n * v0)).
repeat rewrite (mult_comm (c + n * u0));
 repeat rewrite (mult_comm (d + n * v0)).
repeat rewrite <- mult_plus_distr_r.
repeat rewrite (mult_comm n); rewrite H; auto.
Qed.
 
Lemma cong_pow :
 forall a b c : nat, congruent a b -> congruent (power a c) (power b c).
intros a b c; elim c; simpl in |- *; auto.
intros H'; apply cong_ref.
intros n0 H' H'0.
apply cong_mult; auto.
Qed.
 
Theorem congruent' :
 forall a b : nat, b <= a -> congruent a b -> exists k : nat, a = k * n + b.
intros a b H' H'0; inversion_clear H'0.
exists (v - u).
rewrite mult_minus_distr_r; auto.
rewrite plus_minus_assoc.
rewrite plus_comm; rewrite <- H; rewrite plus_comm; auto with arith.
apply le_plus_le with (a := b) (b := a); auto.
Qed.
 
Lemma cong1_le : forall x : nat, 1 < n -> congruent x 1 -> 1 <= x.
Proof.
intros x; case x; auto with arith.
intros H' H'0; inversion_clear H'0.
absurd (n = 1).
red in |- *; intros H'0; absurd (1 < n); auto; rewrite H'0; auto with arith.
apply mult_SO with (y := u - v); auto.
rewrite mult_comm.
rewrite mult_minus_distr_r; auto.
simpl in H; rewrite H.
rewrite <- minus_Sn_m; auto with arith.
Qed.
 
Lemma divides_cong : forall x : nat, divides n x -> congruent 0 x.
Proof.
intros x H; inversion_clear H.
apply congruentDef with (u := q) (v := 0); simpl in |- *; rewrite H0;
 auto with arith.
Qed.
 
Theorem cong_divides :
 forall a b : nat, b <= a -> congruent a b -> divides n (a - b).
Proof.
intros a b H H0; elim (congruent' _ _ H H0).
intros x H1; exists x.
apply plus_reg_l with b.
rewrite le_plus_minus_r; auto.
rewrite plus_comm; rewrite <- H1; auto.
Qed.
End CD.