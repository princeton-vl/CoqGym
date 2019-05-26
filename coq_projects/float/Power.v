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


(****************************************************************************
                                                                             
          IEEE754  :  Rpower                                                 
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  Definition of an exponential function over relative numbers *)
Require Import Omega.
Require Import Reals.
Require Import Zpower.
Require Import ZArith.
Require Import Digit.
Require Import Faux.
Require Import sTactic.
(* We have already an exponential over natural number,
   we prove some basic properties for this function *)
 
Theorem pow_O : forall e : R, (e ^ 0)%R = 1%R.
simpl in |- *; auto with real.
Qed.
 
Theorem pow_1 : forall e : R, (e ^ 1)%R = e.
simpl in |- *; auto with real.
Qed.
 
Theorem pow_NR0 : forall (e : R) (n : nat), e <> 0%R -> (e ^ n)%R <> 0%R.
intros e n; elim n; simpl in |- *; auto with real.
Qed.
 
Theorem pow_add :
 forall (e : R) (n m : nat), (e ^ (n + m))%R = (e ^ n * e ^ m)%R.
intros e n; elim n; simpl in |- *; auto with real.
intros n0 H' m; rewrite H'; auto with real.
Qed.
Hint Resolve pow_O pow_1 pow_NR0 pow_add: real.
 
Theorem pow_RN_plus :
 forall (e : R) (n m : nat),
 e <> 0%R -> (e ^ n)%R = (e ^ (n + m) * / e ^ m)%R.
intros e n; elim n; simpl in |- *; auto with real.
intros n0 H' m H'0.
rewrite Rmult_assoc; rewrite <- H'; auto.
Qed.
 
Theorem pow_lt : forall (e : R) (n : nat), (0 < e)%R -> (0 < e ^ n)%R.
intros e n; elim n; simpl in |- *; auto with real.
intros n0 H' H'0; replace 0%R with (e * 0)%R; auto with real.
Qed.
Hint Resolve pow_lt: real.
 
Theorem Rlt_pow_R1 :
 forall (e : R) (n : nat), (1 < e)%R -> 0 < n -> (1 < e ^ n)%R.
intros e n; elim n; simpl in |- *; auto with real.
intros H' H'0; Contradict H'0; auto with arith.
intros n0; case n0.
simpl in |- *; rewrite Rmult_1_r; auto.
intros n1 H' H'0 H'1.
replace 1%R with (1 * 1)%R; auto with real.
apply Rlt_trans with (r2 := (e * 1)%R); auto with real.
apply Rmult_lt_compat_l; auto with real.
apply Rlt_trans with (r2 := 1%R); auto with real.
apply H'; auto with arith.
Qed.
Hint Resolve Rlt_pow_R1: real.
 
Theorem Rlt_pow :
 forall (e : R) (n m : nat), (1 < e)%R -> n < m -> (e ^ n < e ^ m)%R.
intros e n m H' H'0; replace m with (m - n + n).
rewrite pow_add.
pattern (e ^ n)%R at 1 in |- *; replace (e ^ n)%R with (1 * e ^ n)%R;
 auto with real.
apply Rminus_lt.
repeat rewrite (fun x : R => Rmult_comm x (e ^ n));
 rewrite <- Rmult_minus_distr_l.
replace 0%R with (e ^ n * 0)%R; auto with real.
apply Rmult_lt_compat_l; auto with real.
apply pow_lt; auto with real.
apply Rlt_trans with (r2 := 1%R); auto with real.
apply Rlt_minus; auto with real.
apply Rlt_pow_R1; auto with arith.
apply plus_lt_reg_l with (p := n); auto with arith.
rewrite le_plus_minus_r; auto with arith; rewrite <- plus_n_O; auto.
rewrite plus_comm; auto with arith.
Qed.
Hint Resolve Rlt_pow: real.
 
Theorem pow_R1 :
 forall (r : R) (n : nat), (r ^ n)%R = 1%R -> Rabs r = 1%R \/ n = 0.
intros r n H'.
case (Req_dec (Rabs r) 1); auto; intros H'1.
case (Rdichotomy _ _ H'1); intros H'2.
generalize H'; case n; auto.
intros n0 H'0.
cut (r <> 0%R); [ intros Eq1 | idtac ].
2: Contradict H'0; auto with arith.
2: simpl in |- *; rewrite H'0; rewrite Rmult_0_l; auto with real.
cut (Rabs r <> 0%R); [ intros Eq2 | apply Rabs_no_R0 ]; auto.
absurd (Rabs (/ r) ^ 0 < Rabs (/ r) ^ S n0)%R; auto.
replace (Rabs (/ r) ^ S n0)%R with 1%R.
simpl in |- *; apply Rlt_irrefl; auto.
rewrite Rabs_Rinv; auto.
rewrite <- Rinv_pow; auto.
rewrite RPow_abs; auto.
rewrite H'0; rewrite Rabs_right; auto with real.
apply Rlt_pow; auto with arith.
rewrite Rabs_Rinv; auto.
apply Rmult_lt_reg_l with (r := Rabs r).
case (Rabs_pos r); auto.
intros H'3; case Eq2; auto.
rewrite Rmult_1_r; rewrite Rinv_r; auto with real.
generalize H'; case n; auto.
intros n0 H'0.
cut (r <> 0%R); [ intros Eq1 | auto with real ].
2: Contradict H'0; simpl in |- *; rewrite H'0; rewrite Rmult_0_l;
    auto with real.
cut (Rabs r <> 0%R); [ intros Eq2 | apply Rabs_no_R0 ]; auto.
absurd (Rabs r ^ 0 < Rabs r ^ S n0)%R; auto with real arith.
repeat rewrite RPow_abs; rewrite H'0; simpl in |- *; auto with real.
Qed.
 
Theorem Zpower_NR0 :
 forall (e : BinInt.Z) (n : nat), (0 <= e)%Z -> (0 <= Zpower_nat e n)%Z.
intros e n; elim n; unfold Zpower_nat in |- *; simpl in |- *;
 auto with zarith.
Qed.
 
Theorem Zpower_NR1 :
 forall (e : BinInt.Z) (n : nat), (1 <= e)%Z -> (1 <= Zpower_nat e n)%Z.
intros e n; elim n; unfold Zpower_nat in |- *; simpl in |- *;
 auto with zarith.
Qed.
Hint Resolve Zpower_NR0 Zpower_NR1: zarith.
(* To define exponential over relative number, we simply do 
   a case analysis on the sign of the number *)
 
Definition powerRZ (e : R) (n : BinInt.Z) :=
  match n with
  | BinInt.Z0 => 1%R
  | BinInt.Zpos p => (e ^ BinPos.nat_of_P p)%R
  | BinInt.Zneg p => (/ e ^ BinPos.nat_of_P p)%R
  end.
(* we now prove some basic properties of our exponential *)
 
Theorem powerRZ_O : forall e : R, powerRZ e 0 = 1%R.
simpl in |- *; auto.
Qed.
 
Theorem powerRZ_1 : forall e : R, powerRZ e (Zsucc 0) = e.
simpl in |- *; auto with real.
Qed.
 
Theorem powerRZ_NOR :
 forall (e : R) (z : BinInt.Z), e <> 0%R -> powerRZ e z <> 0%R.
intros e z; case z; simpl in |- *; auto with real.
Qed.
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR: real.
 
Theorem powerRZ_add :
 forall (e : R) (n m : BinInt.Z),
 e <> 0%R -> powerRZ e (n + m) = (powerRZ e n * powerRZ e m)%R.
intros e n m; case n; case m; simpl in |- *; auto with real.
intros n1 m1; rewrite Pnat.nat_of_P_plus_morphism; auto with real.
intros n1 m1. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare m1 n1 Datatypes.Eq); simpl in |- *;
 auto with real.
intros H' H'0; rewrite BinPos.Pcompare_Eq_eq with (1 := H'); auto with real.
intros H' H'0; rewrite (Pnat.nat_of_P_minus_morphism n1 m1); auto with real.
rewrite
 (pow_RN_plus e (BinPos.nat_of_P n1 - BinPos.nat_of_P m1)
    (BinPos.nat_of_P m1)); auto with real.
rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
rewrite Rinv_mult_distr; auto with real.
rewrite Rinv_involutive; auto with real.
apply lt_le_weak.
apply Pnat.nat_of_P_lt_Lt_compare_morphism; auto.
apply BinPos.ZC2; auto.
intros H' H'0; rewrite (Pnat.nat_of_P_minus_morphism m1 n1); auto with real.
rewrite
 (pow_RN_plus e (BinPos.nat_of_P m1 - BinPos.nat_of_P n1)
    (BinPos.nat_of_P n1)); auto with real.
rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
apply lt_le_weak.
change (BinPos.nat_of_P m1 > BinPos.nat_of_P n1) in |- *.
apply Pnat.nat_of_P_gt_Gt_compare_morphism; auto.
intros n1 m1. rewrite Z.pos_sub_spec; unfold Pos.compare.
CaseEq (Pcompare n1 m1 Datatypes.Eq); simpl in |- *;
 auto with real.
intros H' H'0; rewrite BinPos.Pcompare_Eq_eq with (1 := H'); auto with real.
intros H' H'0; rewrite (Pnat.nat_of_P_minus_morphism m1 n1); auto with real.
rewrite
 (pow_RN_plus e (BinPos.nat_of_P m1 - BinPos.nat_of_P n1)
    (BinPos.nat_of_P n1)); auto with real.
rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
rewrite Rinv_mult_distr; auto with real.
apply lt_le_weak.
apply Pnat.nat_of_P_lt_Lt_compare_morphism; auto.
apply BinPos.ZC2; auto.
intros H' H'0; rewrite (Pnat.nat_of_P_minus_morphism n1 m1); auto with real.
rewrite
 (pow_RN_plus e (BinPos.nat_of_P n1 - BinPos.nat_of_P m1)
    (BinPos.nat_of_P m1)); auto with real.
rewrite plus_comm; rewrite le_plus_minus_r; auto with real.
apply lt_le_weak.
change (BinPos.nat_of_P n1 > BinPos.nat_of_P m1) in |- *.
apply Pnat.nat_of_P_gt_Gt_compare_morphism; auto.
intros n1 m1; rewrite Pnat.nat_of_P_plus_morphism; auto with real.
intros H'; rewrite pow_add; auto with real.
apply Rinv_mult_distr; auto.
apply pow_NR0; auto.
apply pow_NR0; auto.
Qed.
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add: real.
 
Theorem powerRZ_Zopp :
 forall (e : R) (z : BinInt.Z),
 e <> 0%R -> powerRZ e (- z) = (/ powerRZ e z)%R.
intros e z H; case z; simpl in |- *; auto with real.
intros p; apply sym_eq; apply Rinv_involutive.
apply pow_nonzero; auto.
Qed.

Theorem powerRZ_Zs :
 forall (e : R) (n : BinInt.Z),
 e <> 0%R -> powerRZ e (Zsucc n) = (e * powerRZ e n)%R.
intros e n H'0.
replace (Zsucc n) with (n + Zsucc 0)%Z.
rewrite powerRZ_add; auto.
rewrite powerRZ_1.
rewrite Rmult_comm; auto.
auto with zarith.
Qed.
(* Conversion theorem between relative numbers and reals *)
 
Theorem Zpower_nat_powerRZ :
 forall (n : BinInt.Z) (m : nat),
 IZR (Zpower_nat n m) = powerRZ (IZR n) (Z_of_nat m).
intros n m; elim m; simpl in |- *; auto with real.
intros m1 H'; rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ; simpl in |- *.
replace (Zpower_nat n (S m1)) with (n * Zpower_nat n m1)%Z.
rewrite Rmult_IZR; auto with real.
rewrite H'; simpl in |- *.
case m1; simpl in |- *; auto with real.
intros m2; rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ; auto.
unfold Zpower_nat in |- *; auto.
Qed.
 
Theorem powerRZ_lt :
 forall (e : R) (z : BinInt.Z), (0 < e)%R -> (0 < powerRZ e z)%R.
intros e z; case z; simpl in |- *; auto with real.
Qed.
Hint Resolve powerRZ_lt: real.
 
Theorem powerRZ_le :
 forall (e : R) (z : BinInt.Z), (0 < e)%R -> (0 <= powerRZ e z)%R.
intros e z H'; apply Rlt_le; auto with real.
Qed.
Hint Resolve powerRZ_le: real.
 
Theorem Rlt_powerRZ :
 forall (e : R) (n m : BinInt.Z),
 (1 < e)%R -> (n < m)%Z -> (powerRZ e n < powerRZ e m)%R.
intros e n m; case n; case m; simpl in |- *;
 try (unfold Zlt in |- *; intros; discriminate); auto with real.
intros p p0 H' H'0; apply Rlt_pow; auto with real.
apply Pnat.nat_of_P_lt_Lt_compare_morphism; auto.
intros p H' H'0; replace 1%R with (/ 1)%R; auto with real.
intros p p0 H' H'0; apply Rlt_trans with (r2 := 1%R).
replace 1%R with (/ 1)%R; auto with real.
apply Rlt_pow_R1; auto with real.
intros p p0 H' H'0; apply Rinv_1_lt_contravar; auto with real.
apply Rlt_pow; auto with real.
apply Pnat.nat_of_P_lt_Lt_compare_morphism; rewrite BinPos.ZC4; auto.
Qed.
Hint Resolve Rlt_powerRZ: real.
 
Theorem Rpow_R1 :
 forall (r : R) (z : BinInt.Z),
 r <> 0%R -> powerRZ r z = 1%R -> Rabs r = 1%R \/ z = 0%Z.
intros r z; case z; simpl in |- *; auto; intros p H' H'1; left.
case (pow_R1 _ _ H'1); auto.
intros H'0; Contradict H'0; auto with zarith; apply convert_not_O.
rewrite Rinv_pow in H'1; auto.
case (pow_R1 _ _ H'1); auto.
intros H'0.
rewrite <- H'0.
apply Rmult_eq_reg_l with (r := 1%R); auto with real.
pattern 1%R at 1 in |- *; rewrite <- H'0; auto with real.
pattern (Rabs (/ r)) at 1 in |- *; rewrite Rabs_Rinv; try rewrite Rinv_l;
 auto with real.
rewrite H'0; auto with real.
apply Rabs_no_R0; auto.
intros H'0; Contradict H'0; auto with zarith; apply convert_not_O.
Qed.
 
Theorem Rpow_eq_inv :
 forall (r : R) (p q : BinInt.Z),
 r <> 0%R -> Rabs r <> 1%R -> powerRZ r p = powerRZ r q -> p = q.
intros r p q H' H'0 H'1.
cut (powerRZ r (p - q) = 1%R); [ intros Eq0 | idtac ].
case (Rpow_R1 _ _ H' Eq0); auto with zarith.
intros H'2; case H'0; auto.
apply Rmult_eq_reg_l with (r := powerRZ r q); auto with real.
rewrite <- powerRZ_add; auto.
replace (q + (p - q))%Z with p; auto with zarith.
rewrite <- H'1; rewrite Rmult_1_r; auto with arith.
Qed.
 
Theorem Zpower_nat_powerRZ_absolu :
 forall n m : BinInt.Z,
 (0 <= m)%Z -> IZR (Zpower_nat n (Zabs_nat m)) = powerRZ (IZR n) m.
intros n m; case m; simpl in |- *; auto with zarith.
intros p H'; elim (BinPos.nat_of_P p); simpl in |- *; auto with zarith.
intros n0 H'0; rewrite <- H'0; simpl in |- *; auto with zarith.
rewrite <- Rmult_IZR; auto.
intros p H'; Contradict H'; auto with zarith.
Qed.
 
Theorem powerRZ_R1 : forall n : BinInt.Z, powerRZ 1 n = 1%R.
intros n; case n; simpl in |- *; auto.
intros p; elim (BinPos.nat_of_P p); simpl in |- *; auto; intros n0 H';
 rewrite H'; ring.
intros p; elim (BinPos.nat_of_P p); simpl in |- *.
exact Rinv_1.
intros n1 H'; rewrite Rinv_mult_distr; try rewrite Rinv_1; try rewrite H';
 auto with real.
Qed.
 
Theorem Rle_powerRZ :
 forall (e : R) (n m : BinInt.Z),
 (1 <= e)%R -> (n <= m)%Z -> (powerRZ e n <= powerRZ e m)%R.
intros e n m H' H'0.
case H'; intros E1.
case (Zle_lt_or_eq _ _ H'0); intros E2.
apply Rlt_le; auto with real.
rewrite <- E2; auto with real.
repeat rewrite <- E1; repeat rewrite powerRZ_R1; auto with real.
Qed.
 
Theorem Zlt_powerRZ :
 forall (e : R) (n m : BinInt.Z),
 (1 <= e)%R -> (powerRZ e n < powerRZ e m)%R -> (n < m)%Z.
intros e n m H' H'0.
case (Zle_or_lt m n); auto; intros Z1.
Contradict H'0.
apply Rle_not_lt.
apply Rle_powerRZ; auto.
Qed.