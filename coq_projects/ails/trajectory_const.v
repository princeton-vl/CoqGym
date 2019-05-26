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


Require Import Reals.
Require Export pi_ineq.

(* Some usefull constants *)
Definition g : R := (322 / 10)%R.
Definition ConflictRange : R := 200%R.
Definition MinSpeed : R := 201%R.
Definition MaxSpeed : R := 880%R.
Definition MaxBank : R := (61 / 100)%R.

(**********)
Record TypeSpeed : Type := mkTypeSpeed
  {v :> R; v_cond1 : (MinSpeed <= v)%R; v_cond2 : (v <= MaxSpeed)%R}.

Definition tan_lb_MaxBank : R := (6 / 10)%R.
Definition tan_ub_MaxBank : R := (7 / 10)%R.

(**********)
Lemma tanBank_def :
 forall x : R, (- MaxBank <= x)%R -> (x <= MaxBank)%R -> cos x <> 0%R.
intros; cut (MaxBank < PI / 2)%R.
intro H1; generalize (Ropp_lt_gt_contravar MaxBank (PI / 2) H1); intro H2;
 generalize (Rle_lt_trans x MaxBank (PI / 2) H0 H1); 
 intro H3; generalize (Rlt_le_trans (- (PI / 2)) (- MaxBank) x H2 H);
 intro H4; generalize (cos_gt_0 x H4 H3); intro H5; 
 red in |- *; intro H6; rewrite H6 in H5; elim (Rlt_irrefl 0 H5).
apply Rlt_trans with (PI_lb / 2)%R.
apply Rlt_trans with 1%R.
unfold MaxBank in |- *; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 100%R.
prove_sup.
rewrite Rmult_1_r; rewrite Rmult_comm; rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym.
prove_sup.
discrR.
unfold PI_lb in |- *; apply Rmult_lt_reg_l with 2%R.
prove_sup.
rewrite Rmult_1_r; unfold Rdiv in |- *; rewrite Rmult_comm;
 rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
prove_sup.
discrR.
unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2%R.
prove_sup.
do 2 rewrite (Rmult_comm 2); do 2 rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
do 2 rewrite Rmult_1_r; elim PI_approx; intros; assumption.
discrR.
Qed.

(* Verifiable in MuPAD*)
Axiom tan_MaxBank_approx : (tan_lb_MaxBank < tan MaxBank < tan_ub_MaxBank)%R.

Lemma tan_MaxBank_ub : (tan MaxBank < tan_ub_MaxBank)%R.
generalize tan_MaxBank_approx; intro H; elim H; intros H0 H1; assumption.
Qed.

Lemma tan_MaxBank_lb : (tan_lb_MaxBank < tan MaxBank)%R.
generalize tan_MaxBank_approx; intro H; elim H; intros H0 H1; assumption.
Qed.

(**********)
Lemma tan_MaxBank_pos : (0 < tan MaxBank)%R.
apply Rlt_trans with tan_lb_MaxBank.
unfold tan_lb_MaxBank in |- *; unfold Rdiv in |- *;
 apply Rmult_lt_reg_l with 10%R.
prove_sup.
rewrite Rmult_0_r; rewrite <- Rmult_comm; repeat rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym.
prove_sup.
discrR.
apply tan_MaxBank_lb.
Qed.