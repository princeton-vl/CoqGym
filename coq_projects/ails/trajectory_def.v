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

Record Trajectory : Type := mkTrajectory
  {x : Differential;
   y : Differential;
   theta : Differential;
   phi : Differential;
   h : TypeSpeed;
   cond_x :
    forall t : R, derive_pt x t (cond_diff x t) = (h * cos (theta t))%R;
   cond_y :
    forall t : R, derive_pt y t (cond_diff y t) = (h * sin (theta t))%R;
   cond_phi : forall t : R, (- MaxBank <= phi t <= MaxBank)%R;
   cond_theta :
    forall t : R,
    derive_pt theta t (cond_diff theta t) = (g * (tan (phi t) / h))%R}.

Record EvaderTrajectory : Type := mkEvaderTrajectory
  {tr : Trajectory;
   tr_cond1 : forall t : R, x tr t = (x tr 0 + h tr * t)%R;
   tr_cond2 : forall t : R, y tr t = y tr 0%R;
   tr_cond3 : forall t : R, theta tr t = 0%R;
   tr_cond4 : forall t : R, phi tr t = 0%R}.

Lemma init_tr_derivable_x :
 forall h : TypeSpeed, derivable (fun t : R => (h * t)%R).
intro; reg.
Qed.

Lemma init_tr_derivable_y :
 forall h : TypeSpeed, derivable (fun t : R => 0%R).
intro; reg.
Qed.

Lemma init_tr_cond_x :
 forall (h : TypeSpeed) (t : R),
 derive_pt (fun t : R => (h * t)%R) t (init_tr_derivable_x h t) =
 (h * cos ((fun t : R => 0) t))%R.
intros; reg.
rewrite cos_0; ring.
Qed.

Lemma init_tr_cond_y :
 forall (h : TypeSpeed) (t : R),
 derive_pt (fun t : R => 0%R) t (init_tr_derivable_y h t) =
 (h * sin ((fun t : R => 0) t))%R.
intros; reg.
rewrite sin_0; ring.
Qed.

Lemma init_tr_cond_phi :
 forall t : R,
 (- MaxBank <= (fun t : R => 0) t)%R /\ ((fun t : R => 0) t <= MaxBank)%R.
intros; simpl in |- *; cut (0 < MaxBank)%R.
split.
left; rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; assumption.
left; assumption.
unfold MaxBank in |- *; unfold Rdiv in |- *; apply Rmult_lt_0_compat;
 [ prove_sup | apply Rinv_0_lt_compat; prove_sup ].
Qed.

Lemma fct_der1 : forall t : R, derivable_pt (fun t : R => 0%R) t.
intro; reg.
Qed.

Lemma init_tr_cond_theta :
 forall (h : TypeSpeed) (t : R),
 derive_pt (fun t : R => 0%R) t (init_tr_derivable_y h t) =
 (fun t : R => (g * (tan 0 / h))%R) t.
intros; reg.
unfold Rdiv in |- *; rewrite tan_0; ring.
Qed.

(**********)
Definition init_tr (h : TypeSpeed) : Trajectory :=
  mkTrajectory
    (mkDifferential (fun t : R => (h * t)%R) (init_tr_derivable_x h))
    (mkDifferential (fun t : R => 0%R) (init_tr_derivable_y h))
    (mkDifferential (fun t : R => 0%R) (init_tr_derivable_y h))
    (mkDifferential (fun t : R => 0%R) (init_tr_derivable_y h)) h
    (init_tr_cond_x h) (init_tr_cond_y h) init_tr_cond_phi
    (init_tr_cond_theta h).

(**********)
Lemma MaxBank_encadr : (0 < MaxBank < PI / 4)%R.
split.
unfold MaxBank in |- *; unfold Rdiv in |- *; apply Rmult_lt_0_compat;
 [ prove_sup | apply Rinv_0_lt_compat; prove_sup ].
apply Rlt_trans with (PI_lb / 4)%R.
unfold MaxBank in |- *; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 100%R.
prove_sup0.
rewrite <- Rmult_comm; rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
rewrite Rmult_1_r; apply Rmult_lt_reg_l with 4%R.
prove_sup.
repeat rewrite (Rmult_comm 4); repeat rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym.
unfold PI_lb in |- *; prove_sup.
discrR.
discrR.
unfold Rdiv in |- *; repeat rewrite <- (Rmult_comm (/ 4));
 apply Rmult_lt_compat_l.
apply Rinv_0_lt_compat; prove_sup.
elim PI_approx; trivial.
Qed.

(**********)
Lemma dtheta_rho :
 forall (tr : Trajectory) (t : R),
 (- rho (h tr) <= derive_pt (theta tr) t (cond_diff (theta tr) t) <=
  rho (h tr))%R.
intros; generalize (cond_theta tr0); intro; rewrite (H t); unfold rho in |- *;
 generalize (cond_phi tr0); intro; elim (H0 t); intros H1 H2;
 generalize MaxBank_encadr; intro H3; elim H3; intros H4 H5; 
 split.
unfold Rdiv in |- *;
 replace (- (g * (tan MaxBank * / h tr0)))%R with
  (g * (- tan MaxBank * / h tr0))%R.
apply Rmult_le_compat_l.
left; apply g_pos.
  setoid_rewrite Rmult_comm at 1 2.
  apply Rmult_le_compat_l.
left; apply (Rinv_0_lt_compat (h tr0) (TypeSpeed_pos (h tr0))).
rewrite <- tan_neg.
generalize
 (Rlt_le (- (PI / 4)) (- MaxBank) (Ropp_lt_gt_contravar MaxBank (PI / 4) H5));
 intro H6; generalize (Ropp_lt_gt_contravar 0 MaxBank H4); 
 rewrite Ropp_0; intro H7;
 generalize
  (Rlt_le (- MaxBank) (PI / 4)
     (Rlt_trans (- MaxBank) 0 (PI / 4) H7 PI4_RGT_0)); 
 intro H8;
 generalize
  (Rlt_le (phi tr0 t) (PI / 4)
     (Rle_lt_trans (phi tr0 t) MaxBank (PI / 4) H2 H5)); 
 intro H9; generalize (Rle_trans (- (PI / 4)) (- MaxBank) (phi tr0 t) H6 H1);
 intro H10; apply tan_incr_1; assumption.
replace (- tan MaxBank)%R with (-1 * tan MaxBank)%R.
repeat rewrite <- Rmult_assoc; rewrite <- (Rmult_comm (-1));
 repeat rewrite <- Rmult_assoc;
 replace (- (g * tan MaxBank * / h tr0))%R with
  (-1 * g * tan MaxBank * / h tr0)%R; [ reflexivity | ring ].
ring.
apply Rmult_le_compat_l;
 [ left; apply g_pos
 | unfold Rdiv in |- *; rewrite (Rmult_comm (tan MaxBank));
    rewrite (Rmult_comm (tan (phi tr0 t))); apply Rmult_le_compat_l;
    [ left; apply (Rinv_0_lt_compat (h tr0) (TypeSpeed_pos (h tr0)))
    | generalize (Rlt_le MaxBank (PI / 4) H5); intro H6;
       generalize (Rle_trans (phi tr0 t) MaxBank (PI / 4) H2 H6); 
       intro H7; generalize PI4_RGT_0; intro H8;
       generalize (Ropp_lt_gt_contravar 0 (PI / 4) H8); 
       rewrite Ropp_0; intro H9;
       generalize
        (Rlt_le (- (PI / 4)) MaxBank (Rlt_trans (- (PI / 4)) 0 MaxBank H9 H4));
       intro H10; generalize (Ropp_le_ge_contravar MaxBank (PI / 4) H6);
       intro H11; generalize (Rge_le (- MaxBank) (- (PI / 4)) H11); 
       intro H12;
       generalize (Rle_trans (- (PI / 4)) (- MaxBank) (phi tr0 t) H12 H1);
       intro H13; apply tan_incr_1; assumption ] ].
Qed.