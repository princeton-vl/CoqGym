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
Require Import trajectory_const.
Require Import rrho.
Require Import constants.
Require Import Omega.

(* Verifiable in MuPAD *)
Axiom
  Math_prop_alarm_1 :
    forall (a l : R) (T : TimeT),
    (MinDistance T <= l)%R ->
    (l <= MaxDistance T)%R ->
    (0 <= a)%R ->
    (a <= MinBeta)%R ->
    (Rsqr (l * cos a - v V * T) + Rsqr (l * sin a) <= Rsqr AlertRange)%R.

(* Verifiable in MuPAD *)
Axiom
  Math_prop_no_conflict_1 :
    forall (a l x y : R) (T : TimeT),
    (MinDistance T <= l)%R ->
    (l <= MaxDistance T)%R ->
    (MinBeta <= a)%R ->
    (a <= PI / 2)%R ->
    (l * sin a + r_V * (cos (rho_V * T) - 1) <= y)%R ->
    (r_V * sin (rho_V * T) - l * cos a <= x)%R ->
    (Rsqr ConflictRange < Rsqr x + Rsqr y)%R.

(**********)
Lemma MinBeta_pos : (0 < MinBeta)%R.
unfold MinBeta in |- *; unfold Rdiv in |- *.
apply Rmult_lt_0_compat; [ prove_sup | apply Rinv_0_lt_compat; prove_sup ].
Qed.

(**********)
Lemma Math_prop_y_a_PI2 :
 forall (a l : R) (T : TimeT),
 (MinBeta <= a)%R ->
 (a <= PI / 2)%R ->
 (0 <= l)%R ->
 (l * sin MinBeta + r_V * (cos (rho_V * T) - 1) <=
  l * sin a + r_V * (cos (rho_V * T) - 1))%R. 
intros; apply Rplus_le_compat_r; apply Rmult_le_compat_l;
 [ assumption
 | apply sin_incr_1;
    [ left; apply Rlt_trans with 0%R;
       [ apply _PI2_RLT_0 | apply MinBeta_pos ]
    | apply Rle_trans with a; assumption
    | left; apply Rlt_trans with 0%R;
       [ apply _PI2_RLT_0
       | apply Rlt_le_trans with MinBeta; [ apply MinBeta_pos | assumption ] ]
    | assumption
    | assumption ] ].
Qed.

(**********)
Lemma Math_prop_approx_y_a_PI2 :
 forall (a l1 l2 : R) (T : TimeT),
 (0 <= a)%R ->
 (a <= PI / 2)%R ->
 (0 <= l1)%R ->
 (l1 <= l2)%R ->
 (l1 * sin_lb a + r_ub V * (cos_lb (rho_ub V * MaxT) - 1) <=
  l2 * sin a + r_V * (cos (rho_V * T) - 1))%R.
intros; apply Rplus_le_compat.
apply Rle_trans with (l1 * sin a)%R.
apply Rmult_le_compat_l.
assumption.
generalize (SIN a H (Rlt_le a PI (Rle_lt_trans a (PI / 2) PI H0 PI2_Rlt_PI)));
 intro; elim H3; intros; assumption.
apply Rmult_le_compat_r.
apply (sin_ge_0 a H (Rlt_le a PI (Rle_lt_trans a (PI / 2) PI H0 PI2_Rlt_PI))).
assumption.
rewrite <- (Ropp_involutive (r_ub V * (cos_lb (rho_ub V * MaxT) - 1)));
 rewrite <- (Ropp_involutive (r_V * (cos (rho_V * T) - 1)));
 apply Ropp_ge_le_contravar; apply Rle_ge;
 replace (- (r_V * (cos (rho_V * T) - 1)))%R with
  (r_V * (1 - cos (rho_V * T)))%R.
replace (- (r_ub V * (cos_lb (rho_ub V * MaxT) - 1)))%R with
 (r_ub V * (1 - cos_lb (rho_ub V * MaxT)))%R.
apply Rmult_le_compat.
left; apply r_V_is_pos.
apply Rplus_le_reg_l with (cos (rho_V * T)); rewrite Rplus_0_r;
 rewrite Rplus_comm; unfold Rminus in |- *; repeat rewrite Rplus_assoc;
 rewrite Rplus_opp_l; rewrite Rplus_0_r; generalize (COS_bound (rho_V * T));
 intro; elim H3; intros; assumption.
unfold r_V in |- *; left; apply r_ub_0.
apply Rplus_le_reg_l with (Ropp 1); unfold Rminus in |- *;
 repeat rewrite <- Rplus_assoc; repeat rewrite Rplus_opp_l;
 repeat rewrite Rplus_0_l; apply Ropp_ge_le_contravar; 
 apply Rle_ge; apply Rle_trans with (cos (rho_ub V * MaxT)).
cut (- PI / 2 <= rho_ub V * MaxT <= PI / 2)%R.
intro; elim H3; intros; generalize (COS (rho_ub V * MaxT) H4 H5); intro;
 elim H6; intros; assumption.
split.
left; apply Rlt_le_trans with 0%R.
replace (- PI / 2)%R with (- (PI / 2))%R.
apply _PI2_RLT_0.
unfold Rdiv in |- *; symmetry  in |- *; apply Ropp_mult_distr_l_reverse.
apply Rmult_le_pos.
left; apply rho_ub_pos.
left; unfold MaxT in |- *.
prove_sup.
cut (MaxT <= MaxT)%R.
intro; left; apply (rho_ub_t_PI2 V (mkTimeT MaxT MinT_MaxT H3)).
right; reflexivity.
apply cos_decr_1.
left; apply Rmult_lt_0_compat.
apply rho_V_is_pos.
apply Rlt_le_trans with MinT.
apply MinT_is_pos.
apply (cond_1 T).
left; apply Rlt_trans with (PI / 2)%R.
apply (rho_t_PI2 T). 
apply PI2_Rlt_PI.
left; apply Rmult_lt_0_compat.
apply rho_ub_pos.
unfold MaxT in |- *; prove_sup.
left; apply Rlt_trans with (PI / 2)%R.
cut (MaxT <= MaxT)%R.
intro; apply (rho_ub_t_PI2 V (mkTimeT MaxT MinT_MaxT H3)).
right; reflexivity.
apply PI2_Rlt_PI.
apply Rmult_le_compat.
left; apply rho_V_is_pos.
left; apply Rlt_le_trans with MinT; [ apply MinT_is_pos | apply (cond_1 T) ].
left; unfold rho_V in |- *; apply rho_ub_0.
apply (cond_2 T).
ring.
ring.
Qed.

(**********)
Lemma Math_prop_x_a_PI2 :
 forall (a l : R) (T : TimeT),
 (MinBeta <= a)%R ->
 (a <= PI / 2)%R ->
 (0 <= l)%R ->
 (r_V * sin (rho_V * T) - l * cos MinBeta <=
  r_V * sin (rho_V * T) - l * cos a)%R.
intros; unfold Rminus in |- *; apply Rplus_le_compat_l;
 apply Ropp_ge_le_contravar; apply Rle_ge; apply Rmult_le_compat_l;
 [ assumption
 | apply cos_decr_1;
    [ left; apply MinBeta_pos
    | apply Rle_trans with a;
       [ assumption
       | left; apply Rle_lt_trans with (PI / 2)%R;
          [ assumption | apply PI2_Rlt_PI ] ]
    | left; apply Rlt_le_trans with MinBeta;
       [ apply MinBeta_pos | assumption ]
    | left; apply Rle_lt_trans with (PI / 2)%R;
       [ assumption | apply PI2_Rlt_PI ]
    | assumption ] ].
Qed.

(**********)
Lemma Math_prop_approx_x_a_PI2 :
 forall (a l1 l2 : R) (T : TimeT),
 (0 <= a)%R ->
 (a <= PI / 2)%R ->
 (0 <= l1)%R ->
 (l1 <= l2)%R ->
 (r_lb V * sin_lb (rho_lb V * MinT) - l2 * cos_ub a <=
  r_V * sin (rho_V * T) - l1 * cos a)%R.
intros; unfold Rminus in |- *; apply Rplus_le_compat.
apply Rmult_le_compat.
left; unfold r_lb in |- *; unfold Rdiv in |- *; apply Rmult_lt_0_compat;
 [ apply TypeSpeed_pos | apply Rinv_0_lt_compat; apply rho_ub_pos ].
apply sin_lb_ge_0.
left; apply Rmult_lt_0_compat; [ apply rho_lb_pos | apply MinT_is_pos ].
apply Rle_trans with (rho_V * MinT)%R.
apply Rmult_le_compat_r.
left; apply MinT_is_pos.
unfold rho_V in |- *; left; apply rho_lb_0.
cut (MinT <= MinT)%R.
intro; left; apply (rho_t_PI2 (mkTimeT MinT H3 MinT_MaxT)).
right; reflexivity.
unfold r_V in |- *; left; apply r_lb_0.
apply Rle_trans with (sin (rho_lb V * MinT)).
cut (0 <= rho_lb V * MinT <= PI)%R.
intro; elim H3; intros.
generalize (SIN (rho_lb V * MinT) H4 H5); intro; elim H6; intros; assumption.
split.
left; apply Rmult_lt_0_compat.
apply rho_lb_pos.
apply MinT_is_pos.
left; apply Rle_lt_trans with (PI / 2)%R.
apply Rle_trans with (rho_V * MinT)%R.
apply Rmult_le_compat_r.
left; apply MinT_is_pos.
unfold rho_V in |- *; left; apply rho_lb_0.
cut (MinT <= MinT)%R.
intro; left; apply (rho_t_PI2 (mkTimeT MinT H3 MinT_MaxT)).
right; reflexivity.
apply PI2_Rlt_PI.
apply sin_incr_1.
left; apply Rlt_trans with 0%R.
apply _PI2_RLT_0.
apply Rmult_lt_0_compat.
apply rho_lb_pos.
apply MinT_is_pos.
apply Rle_trans with (rho_V * MinT)%R.
apply Rmult_le_compat_r.
left; apply MinT_is_pos.
unfold rho_V in |- *; left; apply rho_lb_0.
cut (MinT <= MinT)%R.
intro; left; apply (rho_t_PI2 (mkTimeT MinT H3 MinT_MaxT)).
right; reflexivity.
left; apply Rlt_trans with 0%R.
apply _PI2_RLT_0.
apply Rmult_lt_0_compat.
apply rho_V_is_pos.
apply Rlt_le_trans with MinT.
apply MinT_is_pos.
apply (cond_1 T).
left; apply (rho_t_PI2 T).
apply Rmult_le_compat.
left; apply rho_lb_pos.
left; apply MinT_is_pos.
left; unfold rho_V in |- *; apply rho_lb_0.
apply (cond_1 T).
apply Ropp_ge_le_contravar; apply Rle_ge.
apply Rmult_le_compat.
assumption.
apply cos_ge_0.
left; apply Rlt_le_trans with 0%R.
apply _PI2_RLT_0.
assumption.
assumption.
assumption.
cut (- PI / 2 <= a)%R.
intro; generalize (COS a H3 H0); intro; elim H4; intros; assumption.
left; apply Rlt_le_trans with 0%R.
replace (- PI / 2)%R with (- (PI / 2))%R.
apply _PI2_RLT_0.
unfold Rdiv in |- *; symmetry  in |- *; apply Ropp_mult_distr_l_reverse.
assumption.
Qed.

(**********)
Lemma Math_prop_no_conflict_2 :
 forall (a l x y : R) (T : TimeT),
 (MinDistance T <= l)%R ->
 (l <= MaxDistance T)%R ->
 (3 * (PI / 2) <= a)%R ->
 (a <= 2 * PI - MinBeta)%R ->
 (y <= l * sin a - r_V * (cos (rho_V * T) - 1))%R ->
 (r_V * sin (rho_V * T) - l * cos a <= x)%R ->
 (Rsqr ConflictRange < Rsqr x + Rsqr y)%R.
intros.
cut (MinBeta <= 2 * PI - a)%R.
cut (2 * PI - a <= PI / 2)%R.
cut (l * sin (2 * PI - a) + r_V * (cos (rho_V * T) - 1) <= - y)%R.
intros; rewrite (Rsqr_neg y);
 apply (Math_prop_no_conflict_1 (2 * PI - a) l x (- y) T H H0 H7 H6 H5).
replace (2 * PI - a)%R with (- a + 2 * INR 1 * PI)%R;
 [ rewrite (cos_period (- a) 1); rewrite cos_neg; assumption | simpl; ring ].
replace (2 * PI - a)%R with (- a + 2 * INR 1 * PI)%R;
 [ rewrite (sin_period (- a) 1); rewrite sin_neg;
    replace (l * - sin a + r_V * (cos (rho_V * T) - 1))%R with
     (- (l * sin a - r_V * (cos (rho_V * T) - 1)))%R;
    [ apply Ropp_ge_le_contravar; apply Rle_ge; assumption | simpl; ring ]
 | simpl; ring ].
generalize (Rplus_le_compat_l (PI / 2 - a) (3 * (PI / 2)) a H1);
 replace (PI / 2 - a + 3 * (PI / 2))%R with (2 * PI - a)%R.
replace (PI / 2 - a + a)%R with (PI / 2)%R.
intro; assumption.
unfold Rminus in |- *; rewrite Rplus_assoc; rewrite Rplus_opp_l;
 rewrite Rplus_0_r; reflexivity. 
rewrite double.
pattern PI at 1 2 in |- *; rewrite double_var.
ring.
generalize (Rplus_le_compat_l (MinBeta - a) a (2 * PI - MinBeta) H2);
 replace (MinBeta - a + (2 * PI - MinBeta))%R with (2 * PI - a)%R;
 [ replace (MinBeta - a + a)%R with MinBeta; [ intro; assumption | ring ]
 | ring ].
Qed.

(**********)
Lemma Math_prop_alarm_2 :
 forall (a l : R) (T : TimeT),
 (MinDistance T <= l)%R ->
 (l <= MaxDistance T)%R ->
 (2 * PI - MinBeta <= a)%R ->
 (a <= 2 * PI)%R ->
 (Rsqr (l * cos a - v V * T) + Rsqr (l * sin a) <= Rsqr AlertRange)%R.
intros.
cut (0 <= 2 * PI - a)%R.
cut (2 * PI - a <= MinBeta)%R.
cut (cos (2 * PI - a) = cos a).
cut (sin (2 * PI - a) = (- sin a)%R).
intros; rewrite Rsqr_mult; rewrite (Rsqr_neg (sin a)); rewrite <- H3;
 rewrite <- H4; rewrite <- Rsqr_mult;
 apply (Math_prop_alarm_1 (2 * PI - a) l T H H0 H6 H5).
replace (2 * PI - a)%R with (- a + 2 * INR 1 * PI)%R;
 [ rewrite (sin_period (- a) 1); apply sin_neg | simpl; ring ].
replace (2 * PI - a)%R with (- a + 2 * INR 1 * PI)%R;
 [ rewrite (cos_period (- a) 1); apply cos_neg | simpl; ring ].
generalize (Rplus_le_compat_l (MinBeta - a) (2 * PI - MinBeta) a H1);
 replace (MinBeta - a + (2 * PI - MinBeta))%R with (2 * PI - a)%R;
 [ replace (MinBeta - a + a)%R with MinBeta; [ intro; assumption | ring ]
 | ring ].
generalize (Rplus_le_compat_r (- a) a (2 * PI) H2); rewrite Rplus_opp_r;
 intro; assumption.
Qed.
