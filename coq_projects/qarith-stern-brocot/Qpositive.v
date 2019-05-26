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


Require Export Arith.
Require Export Compare_dec.
Require Export ArithRing.
Require Export Omega.
Require Export ZArith.
Require Export ZArithRing.
 
Ltac CaseEq f := generalize (refl_equal f); pattern f at -1 in |- *; case f.
 
Inductive Qpositive : Set :=
  | nR : Qpositive -> Qpositive
  | dL : Qpositive -> Qpositive
  | One : Qpositive.
 
Fixpoint Qpositive_i (w : Qpositive) : nat * nat :=
  match w with
  | One => (1, 1)
  | nR w' => match Qpositive_i w' with
             | (p, q) => (p + q, q)
             end
  | dL w' => match Qpositive_i w' with
             | (p, q) => (p, p + q)
             end
  end.
Coercion Z_of_nat : nat >-> Z.
 
Theorem interp_reduced_fraction :
 forall w : Qpositive,
 exists a : Z,
   (exists b : Z, (a * fst (Qpositive_i w) + b * snd (Qpositive_i w))%Z = 1%Z).
intros w; elim w; clear w.
intros w Hrec; elim Hrec; intros a Hrec2; elim Hrec2; intros b; simpl in |- *;
 case (Qpositive_i w); simpl in |- *.
intros p q Heq; exists a; exists (b - a)%Z.
rewrite <- Heq; repeat rewrite Znat.inj_plus; ring.
intros w Hrec; elim Hrec; intros a Hrec2; elim Hrec2; intros b; simpl in |- *;
 case (Qpositive_i w); simpl in |- *.
intros p q Heq; exists (a - b)%Z; exists b.
rewrite <- Heq; repeat rewrite Znat.inj_plus; ring.
exists 1%Z; exists 0%Z; simpl in |- *; omega.
Qed.
 
Fixpoint Qpositive_inv (w : Qpositive) : Qpositive :=
  match w with
  | One => One
  | nR w' => dL (Qpositive_inv w')
  | dL w' => nR (Qpositive_inv w')
  end.
 
Theorem inv_correct :
 forall (w : Qpositive) (p q : nat),
 Qpositive_i w = (p, q) -> Qpositive_i (Qpositive_inv w) = (q, p).
 let T_local :=
  (intros w'; simpl in |- *; case (Qpositive_i w'); intros p' q' Hrec p q Heq;
    rewrite (Hrec p' q'); auto; injection Heq; intros H1 H2; 
    rewrite <- H1; rewrite <- H2; rewrite plus_comm; 
    auto) in
 (intros w; elim w; clear w;
   [ T_local
   | T_local
   | simpl in |- *; intros p q Heq; injection Heq; intros H1 H2;
      rewrite <- H1; rewrite <- H2; auto with * ]). 
Qed.
 
Theorem interp_non_zero :
 forall w : Qpositive,
 exists p : nat, (exists q : nat, Qpositive_i w = (S p, S q)).
simple induction w; simpl in |- *;
 (repeat exists 0; auto; fail) ||
   (intros w' Hrec; elim Hrec; intros p' Hex; elim Hex; intros q' Heq;
     rewrite Heq).
exists (p' + S q'); exists q'; auto.
exists p'; exists (p' + S q'); auto.
Qed.
 
Fixpoint Qpositive_c (p q n : nat) {struct n} : Qpositive :=
  match n with
  | O => One
  | S n' =>
      match p - q with
      | O => match q - p with
             | O => One
             | v => dL (Qpositive_c p v n')
             end
      | v => nR (Qpositive_c v q n')
      end
  end.
 
Theorem minus_O_le : forall n m : nat, n - m = 0 -> n <= m.
intros n; elim n; clear n.
auto with arith.
intros n Hrec m; case m; clear m.
simpl in |- *; intros Heq; discriminate Heq.
simpl in |- *; intros; apply le_n_S; apply Hrec; auto.
Qed.
 
Theorem le_minus_O : forall n m : nat, n <= m -> n - m = 0.
intros n; elim n; clear n.
simpl in |- *; auto.
intros n Hrec m; case m; clear m.
intros Hle; inversion Hle.
intros m' Hle; simpl in |- *; apply Hrec; auto with arith.
Qed.
 
Theorem minus_le : forall m n : nat, m - n <= m.
intros m; elim m.
simpl in |- *; auto.
intros m' Hrec n; case n; simpl in |- *; auto.
Qed.
 
Theorem mult_reg_l : forall n m p : nat, S n * m = S n * p -> m = p.
intros n m; elim m; clear m.
intros p; case p; simpl in |- *.
auto.
intros p'; rewrite <- mult_n_O.
intros H; discriminate H.
intros m' Hrec p; case p.
rewrite <- mult_n_O; simpl in |- *; intros H; discriminate H.
intros p'; repeat rewrite (mult_comm (S n)); simpl in |- *.
intros H; injection H.
intros H'; apply f_equal with (f := S).
apply Hrec.
repeat rewrite (mult_comm (S n)).
apply plus_reg_l with n.
exact H'.
Qed.
 
Theorem absolu_inj_nat : forall x : nat, Z.abs_nat (Z_of_nat x) = x.
intros x; case x.
auto.
simpl in |- *.
exact nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.
 
Theorem absolu_mult :
 forall x y : Z, Z.abs_nat (x * y) = Z.abs_nat x * Z.abs_nat y.
intros x; case x; auto; intros p y; case y; auto; simpl in |- *; intros;
 apply nat_of_P_mult_morphism.
Qed.
 
Theorem Qpositive_c_unfold1 :
 forall p q n : nat,
 S p + S q + S q <= S n ->
 Qpositive_c (S p + S q) (S q) (S n) = nR (Qpositive_c (S p) (S q) n).
intros p q n Hle; simpl in |- *.
rewrite <- (plus_n_Sm p q).
rewrite <- (minus_Sn_m (p + q) q).
rewrite (plus_comm p); rewrite minus_plus; auto with *.
auto with arith.
Qed.
 
Theorem Qpositive_c_unfold2 :
 forall p q n : nat,
 S p + (S p + S q) <= S n ->
 Qpositive_c (S p) (S p + S q) (S n) = dL (Qpositive_c (S p) (S q) n).
intros p q n Hle; simpl in |- *.
rewrite le_minus_O.
rewrite minus_plus.
auto.
auto with arith.
Qed.
 
Theorem construct_correct :
 forall (w : Qpositive) (p q n : nat),
 Qpositive_i w = (p, q) -> p + q <= n -> Qpositive_c p q n = w.
intros w; elim w; clear w.
intros w'; simpl in |- *.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq.
rewrite Heq.
intros Hrec p q n Heq_pair.
injection Heq_pair; intros Heq2 Heq1; rewrite <- Heq2; rewrite <- Heq1.
case n.
simpl in |- *; intros Hle; inversion Hle.
clear n; intros n.
intros Hle.
 replace (Qpositive_c (S (p' + S q')) (S q') (S n)) with
  (nR (Qpositive_c (S p') (S q') n)).
apply f_equal with (f := nR).
apply Hrec; auto with *.
rewrite <- plus_Sn_m.
rewrite Qpositive_c_unfold1. auto with *.
auto with *.
intros w'; simpl in |- *.
elim (interp_non_zero w'); intros p' Hex; elim Hex; intros q' Heq.
rewrite Heq.
intros Hrec p q n Heq_pair.
injection Heq_pair; intros Heq2 Heq1; rewrite <- Heq2; rewrite <- Heq1.
case n.
simpl in |- *; intros Hle; inversion Hle.
clear n; intros n.
intros Hle.
 replace (Qpositive_c (S p') (S (p' + S q')) (S n)) with
  (dL (Qpositive_c (S p') (S q') n)).
apply f_equal with (f := dL).
apply Hrec; auto with *.
rewrite <- plus_Sn_m.
rewrite Qpositive_c_unfold2; auto with *.

simpl in |- *; intros p q n Heq; injection Heq; intros Heq2 Heq1; case n.
rewrite <- Heq1; simpl in |- *; intros Hle; inversion Hle.
rewrite <- Heq1; rewrite <- Heq2; simpl in |- *; auto with *.

Qed.
 
Theorem construct_correct2 :
 forall n p q : nat,
 S p + S q <= n ->
 exists d : nat,
   S p = fst (Qpositive_i (Qpositive_c (S p) (S q) n)) * S d /\
   S q = snd (Qpositive_i (Qpositive_c (S p) (S q) n)) * S d.
intros n; elim n.
intros p q Hle; inversion Hle.
clear n; intros n.
intros Hrec p q Hle; case (le_gt_dec (S p) (S q)).
simpl in |- *.
intros Hle'; rewrite (le_minus_O p q).
CaseEq (q - p).
intros Heq_minus; exists p.
simpl in |- *; split; auto with arith.
rewrite <- plus_n_O.
apply le_antisym; auto with arith.
apply minus_O_le.
auto.
intros q' Heq_minus; elim (Hrec p q').
intros d; simpl in |- *; case (Qpositive_i (Qpositive_c (S p) (S q') n));
 repeat rewrite <- (mult_comm (S d)); intros p'' q'' (Heq1, Heq2).
exists d; split.
exact Heq1.
rewrite (le_plus_minus (S p) (S q)).
simpl in |- *.
rewrite Heq_minus; rewrite Heq2.
simpl in |- *.
replace (S (p + q'' * S d)) with (S p + q'' * S d).
rewrite Heq1.
simpl in |- *.
ring.
simpl in |- *; auto.
auto with arith.
apply le_S_n.
rewrite plus_n_Sm.
apply le_trans with (S p + S q).
apply plus_le_compat_l.
apply le_n_S.
rewrite <- Heq_minus; apply minus_le.
exact Hle.
auto with arith.
intros Hgt; simpl in |- *; CaseEq (p - q).
intros H; elim (gt_not_le _ _ Hgt).
apply le_n_S.
apply minus_O_le.
exact H.
intros p'.
intros Heq_minus; simpl in |- *; elim (Hrec p' q).
intros d; case (Qpositive_i (Qpositive_c (S p') (S q) n)).
simpl in |- *; intros p'' q'' (Heq1, Heq2).
exists d; split; auto.
rewrite (le_plus_minus (S q) (S p)); simpl in |- *.
rewrite Heq_minus.
replace (S (q + S p')) with (S q + S p').
rewrite Heq2; rewrite Heq1; ring.
simpl in |- *; auto.
auto with arith.
rewrite <- Heq_minus.
replace (p - q) with (S p - S q).
rewrite <- (plus_comm (S q)).
rewrite <- (le_plus_minus (S q) (S p)).
apply le_trans with (S p + q).
auto with arith.
apply le_S_n; rewrite plus_n_Sm.
exact Hle.
auto with arith.
auto.
Qed.
 
Theorem construct_correct2' :
 forall n p q : nat,
 1 <= p ->
 1 <= q ->
 p + q <= n ->
 exists d : nat,
   p = fst (Qpositive_i (Qpositive_c p q n)) * S d /\
   q = snd (Qpositive_i (Qpositive_c p q n)) * S d.
intros n p; case p.
intros q H; inversion H.
intros p' q; case q.
intros Hle H; inversion H.
intros q' Hle Hle2; exact (construct_correct2 n p' q').
Qed.
 
Theorem construct_correct3 :
 forall n n' p q p' q' d : nat,
 S p = S d * p' ->
 S q = S d * q' ->
 S p + S q <= S n ->
 p' + q' <= S n' -> Qpositive_c (S p) (S q) (S n) = Qpositive_c p' q' (S n').
intros n; elim n; clear n.
intros n' p q p' q' d; rewrite <- plus_n_Sm.
simpl in |- *.
intros H1 H2 H3; inversion H3.
inversion H0.
intros n0 Hrec n' p q p' q' d Heqd1 Heqd2 Hle1 Hle2.
simpl in |- *.
CaseEq (p - q).
CaseEq (q - p).
intros H H0.
cut (p' = q').
intros Heq'; rewrite Heq'; rewrite <- (minus_n_n q').
auto.
apply mult_reg_l with d.
rewrite <- Heqd2; rewrite <- Heqd1.
apply le_antisym; apply minus_O_le; assumption.
intros q2 Heq2 Heqp.
cut (p' <= q').
intros H; generalize (le_minus_O _ _ H).
intros Heq3; rewrite Heq3.
CaseEq (q' - p').
intros Heq4; cut (q' = p').
intros Heq5; generalize Heq2; replace (q - p) with (S q - S p).
rewrite Heqd2; rewrite Heqd1; rewrite Heq5.
rewrite <- minus_n_n; intros Heq6; discriminate Heq6.
auto.
apply le_antisym; apply minus_O_le; assumption.
intros q'2.
generalize Hle2; case n'.
generalize Heqd1 Heqd2; case p'; case q'.
simpl in |- *; intros H'1 H'2 H'3 H'4; discriminate H'4.
intros x; rewrite <- (mult_comm 0); simpl in |- *; intros Dummy;
 discriminate Dummy.
simpl in |- *; intros x H'1 H'2 H'3 H'4; discriminate H'4.
simpl in |- *; intros n n1 H'1 H'2; rewrite <- plus_n_Sm; intros H'3;
 inversion H'3.
inversion H1.
intros n''.
intros Hle3 Heq4.
simpl in |- *.
CaseEq p'.
intros Heqp'; generalize Heqd1; rewrite Heqp'.
rewrite <- (mult_comm 0); simpl in |- *; intros Dummy; discriminate Dummy.
intros p'2 Heqp'2.
change
  (dL (Qpositive_c (S p) (S q2) (S n0)) =
   dL (Qpositive_c (S p'2) (S q'2) (S n''))) in |- *.
apply f_equal with (f := dL).
apply Hrec with d; auto with *.
rewrite <- Heqp'2; assumption.
rewrite <- Heq4; rewrite <- Heq2; rewrite (mult_comm (S d)).
rewrite mult_minus_distr_r.
repeat rewrite <- (mult_comm (S d)).
rewrite <- Heqd2; rewrite <- Heqd1.
simpl in |- *; auto.
apply mult_S_le_reg_l with d.
rewrite <- Heqd2; rewrite <- Heqd1.
apply le_n_S.
apply minus_O_le; assumption.
intros p2 Heqp2.
CaseEq (p' - q').
intros Heqm'; cut (S p - S q = 0).
simpl in |- *; rewrite Heqp2; intros Dummy; discriminate Dummy.
rewrite Heqd2; rewrite Heqd1.
repeat rewrite (mult_comm (S d)).
rewrite <- mult_minus_distr_r.
rewrite Heqm'; simpl in |- *; auto.
intros p'2.
generalize Hle2; case n'.
generalize Heqd1 Heqd2; case p'; case q'.
simpl in |- *; intros H'1 H'2 H'3 H'4; discriminate H'4.
intros x; rewrite <- (mult_comm 0); simpl in |- *; intros Dummy;
 discriminate Dummy.
intros x; rewrite <- (mult_comm 0); simpl in |- *; intros Dummy1 Dummy2;
 discriminate Dummy2.
simpl in |- *; intros n n1 H'1 H'2; rewrite <- plus_n_Sm; intros H'3;
 inversion H'3.
inversion H0.
intros n''.
intros Hle3 Heq4.
CaseEq q'.
intros Heq5; generalize Heqd2; rewrite Heq5; simpl in |- *.
rewrite <- (mult_comm 0); simpl in |- *; intros Dummy; discriminate Dummy.
intros q'2 Heqq'2.
change
  (nR (Qpositive_c (S p2) (S q) (S n0)) =
   nR (Qpositive_c (S p'2) (S q'2) (S n''))) in |- *.
apply f_equal with (f := nR).
apply Hrec with d; auto with *.
rewrite <- Heq4; rewrite <- Heqp2; rewrite (mult_comm (S d)).
rewrite mult_minus_distr_r.
repeat rewrite <- (mult_comm (S d)).
rewrite <- Heqd2; rewrite <- Heqd1.
simpl in |- *; auto.
rewrite <- Heqq'2; assumption.
Qed.
 
Theorem construct_correct4 :
 forall p q p' q' n n' : nat,
 S p + S q <= S n ->
 S p' + S q' <= S n' ->
 S p * S q' = S p' * S q ->
 Qpositive_c (S p) (S q) (S n) = Qpositive_c (S p') (S q') (S n').
intros p q p' q' n n' H H0 H1.
elim (construct_correct2 _ _ _ H).
intros d (Heq1, Heq2).
elim (construct_correct2 _ _ _ H0).
intros d' (Heq3, Heq4).
elim (interp_non_zero (Qpositive_c (S p) (S q) (S n))).
intros p0 Hex1; elim Hex1; intros q0 Heq5; clear Hex1.
elim (interp_non_zero (Qpositive_c (S p') (S q') (S n'))).
intros p'0 Hex1; elim Hex1; intros q'0 Heq6; clear Hex1.
elim (interp_reduced_fraction (Qpositive_c (S p) (S q) (S n))); intros a Hex1;
 elim Hex1; intros b; clear Hex1.
rewrite Heq6 in Heq4; rewrite Heq6 in Heq3; rewrite Heq5 in Heq2;
 rewrite Heq5 in Heq1; rewrite Heq5; unfold fst, snd in |- *; 
 intros Heq7.
generalize H1; rewrite Heq1; rewrite Heq2; rewrite Heq3; rewrite Heq4;
 unfold fst, snd in |- *; clear H1; intros H1.
unfold fst, snd in Heq1, Heq2, Heq3, Heq4.
cut (S p0 * S q'0 = S p'0 * S q0).
intros Heq8.
cut (S p'0 = Z.abs_nat (a * S p'0 + b * S q'0) * S p0).
intros Heq9.
cut (S q'0 = Z.abs_nat (a * S p'0 + b * S q'0) * S q0).
intros Heq10.
cut (exists d'' : nat, Z.abs_nat (a * S p'0 + b * S q'0) = S d'').
intros Hex; elim Hex; intros d'' Heq11; rewrite Heq11 in Heq9;
 rewrite Heq11 in Heq10.
replace (S p0 * S d) with (S (d + p0 * S d)).
replace (S q0 * S d) with (S (d + q0 * S d)).
rewrite
 (construct_correct3 n n (d + p0 * S d) (d + q0 * S d) (S p0) (S q0) d)
 .
replace (S p'0 * S d') with (S (d' + p'0 * S d')).
replace (S q'0 * S d') with (S (d' + q'0 * S d')).
symmetry  in |- *.
apply construct_correct3 with (d := d' + d'' * S d').
replace (S (d' + p'0 * S d')) with (S p'0 * S d').
rewrite Heq9; ring.
auto.
replace (S (d' + q'0 * S d')) with (S q'0 * S d').
rewrite Heq10; ring.
auto.
replace (S (d' + q'0 * S d')) with (S q'0 * S d').
replace (S (d' + p'0 * S d')) with (S p'0 * S d').
rewrite <- Heq3; rewrite <- Heq4.
exact H0.
auto.
auto.
apply le_trans with (S p + S q).
rewrite Heq1; rewrite Heq2.
rewrite <- mult_plus_distr_r.
rewrite mult_comm; simpl in |- *; auto with arith.
assumption.
auto.
auto.
rewrite (mult_comm (S d)); auto.
rewrite (mult_comm (S d)); auto.
replace (S (d + q0 * S d)) with (S q0 * S d).
replace (S (d + p0 * S d)) with (S p0 * S d).
rewrite <- Heq1; rewrite <- Heq2.
exact H.
auto.
auto.
apply le_trans with (S p + S q).
rewrite Heq1; rewrite Heq2.
rewrite <- mult_plus_distr_r.
rewrite mult_comm; simpl in |- *; auto with arith.
assumption.
auto.
auto.
CaseEq (Z.abs_nat (a * S p'0 + b * S q'0)).
intros Dummy; rewrite Dummy in Heq10; simpl in Heq10; discriminate Heq10.
intros d'' Heq; exists d''; auto.
rewrite <- (absolu_inj_nat (S q0)).
pattern (S q'0) at 1 in |- *; rewrite <- (absolu_inj_nat (S q'0)).
rewrite <- absolu_mult.
apply f_equal with (f := Z.abs_nat).
pattern (Z_of_nat (S q'0)) at 1 in |- *; rewrite <- Zmult_1_r.
rewrite <- Heq7.
replace (S q'0 * (a * S p0 + b * S q0))%Z with
 (S p0 * S q'0 * a + S q'0 * (b * S q0))%Z.
rewrite <- (Znat.inj_mult (S p0)).
rewrite Heq8.
rewrite Znat.inj_mult; ring.
ring.
rewrite <- (absolu_inj_nat (S p0)).
pattern (S p'0) at 1 in |- *; rewrite <- absolu_inj_nat.
rewrite <- absolu_mult.
apply f_equal with (f := Z.abs_nat).
pattern (Z_of_nat (S p'0)) at 1 in |- *; rewrite <- Zmult_1_r.
rewrite <- Heq7.
replace (S p'0 * (a * S p0 + b * S q0))%Z with
 (S p'0 * S q0 * b + S p'0 * (a * S p0))%Z.
rewrite <- (Znat.inj_mult (S p'0)).
rewrite <- Heq8.
rewrite Znat.inj_mult; ring.
ring.
apply mult_reg_l with (d' + d * S d').
replace (S (d' + d * S d')) with (S d * S d').
transitivity (S p0 * S d * (S q'0 * S d')).
ring.
rewrite H1.
ring.
auto.
Qed.
 
Theorem construct_correct4' :
 forall p q p' q' n n' : nat,
 1 <= p ->
 1 <= q ->
 1 <= p' ->
 1 <= q' ->
 p + q <= n ->
 p' + q' <= n' -> p * q' = p' * q -> Qpositive_c p q n = Qpositive_c p' q' n'.
intros p; case p.
intros q p' q' n n' H; inversion H.
intros p0 q; case q.
intros p' q' n n' H H1; inversion H1.
intros q0 p'; case p'.
intros q' n n' H H1 H2; inversion H2.
intros p'0 q'; case q'.
intros n n' H H1 H2 H3; inversion H3.
intros q'0 n; case n.
simpl in |- *; intros n' H H1 H2 H3 H4; inversion H4.
intros n0 n'; case n'.
simpl in |- *; intros H H1 H2 H3 H4 H5; inversion H5.
intros; apply construct_correct4; auto.
Qed.
 
Theorem interp_inject :
 forall w w' : Qpositive, Qpositive_i w = Qpositive_i w' -> w = w'.
intros w w' H; CaseEq (Qpositive_i w).
intros p q Heq.
rewrite <- construct_correct with (1 := Heq) (n := p + q).
apply construct_correct; auto.
rewrite <- H; auto.
auto.
Qed.
 
Theorem minus_decompose :
 forall a b c d : nat, a = b -> c = d -> a - c = b - d.
intros a b c d H H1; rewrite H; rewrite H1; auto.
Qed.
 
Theorem Qpositive_c_equiv :
 forall n p q n' p' q' : nat,
 S p + S q <= n ->
 S p' + S q' <= n' ->
 Qpositive_c (S p) (S q) n = Qpositive_c (S p') (S q') n' ->
 S p * S q' = S p' * S q.
intros n; elim n.
simpl in |- *; intros p q n' p' q' H; inversion H.
intros n0 Hrec p q n'.
case n'.
simpl in |- *; intros p' q' H H1; inversion H1.
unfold Qpositive_c in |- *.
CaseEq (S p - S q).
CaseEq (S q - S p).
intros Heq1 Heq2 n1 p' q'; CaseEq (S p' - S q').
CaseEq (S q' - S p').
intros Heq3 Heq4; cut (p = q).
intros Heq5; rewrite Heq5.
cut (p' = q').
intros Heq6; rewrite Heq6.
intros; apply mult_comm.
apply eq_add_S; apply le_antisym; apply minus_O_le; auto with *.
apply eq_add_S; apply le_antisym; apply minus_O_le; auto with *.
intros p2 H H1 H2 H3 H4; discriminate H4.
intros n2 H H1 H2 H4; discriminate H4.
intros q2 Heq1 Heq2 n2 p' q'; CaseEq (S p' - S q').
CaseEq (S q' - S p').
intros H3 H4 H H1 H2; discriminate H2.
intros q'2 H H1 H2 H3 H4; injection H4; intros H5.
rewrite (le_plus_minus (S p) (S q)).
rewrite (le_plus_minus (S p') (S q')).
rewrite (mult_comm (S p)); rewrite (mult_comm (S p')).
repeat rewrite mult_plus_distr_r; repeat rewrite <- (mult_comm (S p)).
apply f_equal with (f := fun x : nat => S p * S p' + x).
rewrite Heq1; rewrite H.
rewrite <- (mult_comm (S p')).
apply Hrec with n2.
rewrite <- Heq1.
rewrite <- le_plus_minus.
apply le_trans with (p + S q).
auto with arith.
apply le_S_n; exact H2.
apply minus_O_le; auto.
rewrite <- H.
rewrite <- le_plus_minus.
apply le_trans with (p' + S q').
auto with arith; fail.
apply le_S_n; exact H3.
apply minus_O_le; auto.
exact H5.
apply minus_O_le; auto.
apply minus_O_le; auto.
intros n1 dummy1 Dummy2 Dummy3 Dummy; discriminate Dummy.
intros n1 Heq1 n2 p' q' Hle1 Hle2; CaseEq (S p' - S q').
CaseEq (S q' - S p').
intros Dummy3 Dummy1 Dummy2; discriminate Dummy2.
intros n3 Dummy Dummy1 Dummy2; discriminate Dummy2.
intros p'2 Heq2 Heq3.
injection Heq3; clear Heq3; intros Heq3.
rewrite (le_plus_minus (S q) (S p)).
rewrite Heq1.
rewrite (le_plus_minus (S q') (S p')).
rewrite Heq2.
repeat rewrite mult_plus_distr_r; repeat rewrite (mult_comm (S q')).
apply f_equal with (f := fun x : nat => S q * S q' + x).
apply Hrec with n2.
rewrite plus_comm; rewrite <- Heq1.
rewrite <- le_plus_minus.
apply le_trans with (p + S q).
rewrite <- plus_n_Sm.
auto with arith.
apply le_S_n; assumption.
omega.
rewrite <- Heq2.
rewrite plus_comm; rewrite <- le_plus_minus.
apply le_trans with (p' + S q').
rewrite <- plus_n_Sm; auto with arith.
apply le_S_n; exact Hle2.
omega.
exact Heq3.
omega.
omega.
Qed.
 
Theorem Qpositive_c_equiv' :
 forall n p q n' p' q' : nat,
 1 <= p ->
 1 <= q ->
 1 <= p' ->
 1 <= q' ->
 p + q <= n ->
 p' + q' <= n' -> Qpositive_c p q n = Qpositive_c p' q' n' -> p * q' = p' * q.
intros n p q n' p' q'; case p.
intros H; inversion H.
clear p; intros p Hlp.
case q; [ intros H; inversion H | clear q; intros q Dummy; clear Dummy ].
case p'; [ intros H; inversion H | clear p'; intros p' Dummy; clear Dummy ].
case q'; [ intros H; inversion H | clear q'; intros q' Dummy; clear Dummy ].
intros; apply Qpositive_c_equiv with n n'; auto.
Qed.
