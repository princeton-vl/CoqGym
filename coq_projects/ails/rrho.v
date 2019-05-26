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

Definition rho (h : TypeSpeed) : R := (g * (tan MaxBank / h))%R.
Definition r (h : TypeSpeed) : R := (h / rho h)%R.
Definition rho_ub (h : TypeSpeed) : R := (g * (tan_ub_MaxBank / h))%R.
Definition rho_lb (h : TypeSpeed) : R := (g * (tan_lb_MaxBank / h))%R.

(**********)
Lemma TypeSpeed_pos : forall h : TypeSpeed, (0 < h)%R.
intro; assert (H := v_cond1 h).
apply Rlt_le_trans with MinSpeed.
unfold MinSpeed in |- *; prove_sup.
assumption.
Qed.

(**********)
Lemma g_pos : (0 < g)%R.
unfold g in |- *; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 10%R.
prove_sup.
rewrite Rmult_0_r; rewrite <- Rmult_comm; rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym; [ prove_sup | discrR ].
Qed.

(**********)
Lemma rho_ub_0 : forall h : TypeSpeed, (rho h < rho_ub h)%R.
intros; unfold rho, rho_ub in |- *; apply Rmult_lt_compat_l;
 [ apply g_pos
 | generalize TypeSpeed_pos; intros; generalize (H h); clear H; intro H;
    generalize (Rinv_0_lt_compat h H); intro H1; generalize tan_MaxBank_ub;
    intro H2;
    generalize (Rmult_lt_compat_l (/ h) (tan MaxBank) tan_ub_MaxBank H1 H2);
    rewrite Rmult_comm; rewrite <- (Rmult_comm tan_ub_MaxBank); 
    intro H3; assumption ].
Qed.

(**********)
Lemma rho_lb_0 : forall h : TypeSpeed, (rho_lb h < rho h)%R.
intros; unfold rho, rho_lb in |- *; apply Rmult_lt_compat_l;
 [ apply g_pos
 | generalize TypeSpeed_pos; intros; generalize (H h); clear H; intro H;
    generalize (Rinv_0_lt_compat h H); intro H1; generalize tan_MaxBank_lb;
    intro H2;
    generalize (Rmult_lt_compat_l (/ h) tan_lb_MaxBank (tan MaxBank) H1 H2);
    rewrite <- (Rmult_comm (tan MaxBank));
    rewrite <- (Rmult_comm tan_lb_MaxBank); intro H3; 
    assumption ].
Qed.

Definition r_ub (h : TypeSpeed) : R := (h / rho_lb h)%R.
Definition r_lb (h : TypeSpeed) : R := (h / rho_ub h)%R.

(**********)
Lemma tan_lb_MaxBank_pos : (0 < tan_lb_MaxBank)%R.
unfold tan_lb_MaxBank in |- *; unfold Rdiv in |- *;
 apply Rmult_lt_reg_l with 10%R.
prove_sup.
rewrite Rmult_0_r; rewrite <- Rmult_comm; rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym; [ prove_sup | discrR ].
Qed.

(**********)
Lemma tan_ub_MaxBank_pos : (0 < tan_ub_MaxBank)%R.
apply Rlt_trans with tan_lb_MaxBank;
 [ apply tan_lb_MaxBank_pos
 | apply Rlt_trans with (tan MaxBank);
    [ apply tan_MaxBank_lb | apply tan_MaxBank_ub ] ].
Qed.

(**********)
Lemma rho_lb_pos : forall h : TypeSpeed, (0 < rho_lb h)%R.
intros; unfold rho_lb in |- *; apply Rmult_lt_0_compat;
 [ apply g_pos
 | replace (tan_lb_MaxBank / h)%R with (tan_lb_MaxBank * / h)%R;
    [ rewrite Rmult_comm; generalize TypeSpeed_pos; intro H; generalize (H h);
       clear H; intro H; generalize (Rinv_0_lt_compat h H); 
       intro H0; apply Rmult_lt_0_compat;
       [ assumption | apply tan_lb_MaxBank_pos ]
    | auto ] ].
Qed.

(**********)
Lemma rho_pos : forall h : TypeSpeed, (0 < rho h)%R.
intro; apply Rlt_trans with (rho_lb h); [ apply rho_lb_pos | apply rho_lb_0 ].
Qed.

(**********)
Lemma rho_ub_pos : forall h : TypeSpeed, (0 < rho_ub h)%R.
intro; apply Rlt_trans with (rho h); [ apply rho_pos | apply rho_ub_0 ].
Qed.

(**********)
Lemma r_ub_0 : forall h : TypeSpeed, (r h < r_ub h)%R.
intros; unfold r, r_ub in |- *; generalize (rho_lb_0 h); intro H;
 generalize (Rmult_lt_0_compat (rho_lb h) (rho h) (rho_lb_pos h) (rho_pos h));
 intro H0; generalize (Rinv_lt_contravar (rho_lb h) (rho h) H0 H); 
 intro H1;
 generalize (Rmult_lt_compat_l h (/ rho h) (/ rho_lb h) (TypeSpeed_pos h) H1);
 intro H2; assumption.
Qed.

(**********)
Lemma r_lb_0 : forall h : TypeSpeed, (r_lb h < r h)%R.
intros; unfold r, r_lb in |- *; generalize (rho_ub_0 h); intro H;
 generalize (Rmult_lt_0_compat (rho h) (rho_ub h) (rho_pos h) (rho_ub_pos h));
 intro H0; generalize (Rinv_lt_contravar (rho h) (rho_ub h) H0 H); 
 intro H1;
 generalize (Rmult_lt_compat_l h (/ rho_ub h) (/ rho h) (TypeSpeed_pos h) H1);
 intro H2; assumption.
Qed.

(**********)
Lemma rho_PI2 : forall h : TypeSpeed, (rho h <= PI / 2)%R.
intro h; unfold rho in |- *; unfold Rdiv in |- *.
cut (g < 33)%R.
cut (tan MaxBank < 1)%R.
cut (/ h < / 200)%R.
intros; generalize g_pos; intro H2; generalize tan_MaxBank_pos; intro H3;
 generalize (Rinv_0_lt_compat h (TypeSpeed_pos h)); 
 intro H4.
generalize
 (Rmult_le_0_lt_compat g 33 (tan MaxBank) 1 (Rlt_le 0 g H2)
    (Rlt_le 0 (tan MaxBank) H3) H1 H0); intro H5;
 generalize (Rmult_lt_0_compat g (tan MaxBank) H2 H3); 
 intro H6.
rewrite Rmult_1_r in H5.
generalize
 (Rmult_le_0_lt_compat (g * tan MaxBank) 33 (/ h) (/ 200)
    (Rlt_le 0 (g * tan MaxBank) H6) (Rlt_le 0 (/ h) H4) H5 H).
intro H7; left.
apply Rlt_trans with (33 / 200)%R.
unfold Rdiv in |- *; rewrite <- Rmult_assoc; assumption.
apply Rlt_le_trans with (PI_lb / 2)%R.
apply Rlt_trans with 1%R.
unfold Rdiv in |- *; apply Rmult_lt_reg_l with 200%R.
prove_sup.
rewrite Rmult_1_r; rewrite <- Rmult_comm; rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym; [ prove_sup | discrR ].
apply Rmult_lt_reg_l with 2%R.
prove_sup.
unfold Rdiv in |- *; rewrite <- (Rmult_comm (/ 2)); rewrite <- Rmult_assoc;
 rewrite <- Rinv_r_sym.
rewrite Rmult_1_r; rewrite Rmult_1_l; unfold PI_lb in |- *.
prove_sup.
discrR.
unfold Rdiv in |- *; left; repeat rewrite <- (Rmult_comm (/ 2));
 apply Rmult_lt_compat_l.
apply Rinv_0_lt_compat; prove_sup.
elim PI_approx; intros; assumption.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
prove_sup.
apply TypeSpeed_pos.
apply Rlt_le_trans with MinSpeed.
unfold MinSpeed in |- *; prove_sup.
apply (v_cond1 h).
apply Rlt_trans with tan_ub_MaxBank.
apply tan_MaxBank_ub.
unfold tan_ub_MaxBank in |- *; unfold Rdiv in |- *;
 apply Rmult_lt_reg_l with 10%R.
prove_sup.
rewrite <- Rmult_comm; rewrite Rmult_assoc; rewrite <- Rinv_l_sym;
 [ prove_sup | discrR ].
unfold g in |- *; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 10%R.
prove_sup.
rewrite <- Rmult_comm; rewrite Rmult_assoc; rewrite <- Rinv_l_sym;
 [ prove_sup | discrR ].
Qed.

(**********)
Lemma rho_strict_decreasing :
 forall h1 h2 : TypeSpeed, (h1 < h2)%R -> (rho h2 < rho h1)%R.
intros; unfold rho in |- *; apply Rmult_lt_compat_l;
 [ apply g_pos
 | unfold Rdiv in |- *; apply Rmult_lt_compat_l;
    [ apply tan_MaxBank_pos
    | apply
       (Rinv_lt_contravar h1 h2
          (Rmult_lt_0_compat h1 h2 (TypeSpeed_pos h1) (TypeSpeed_pos h2)) H) ] ].
Qed.

(**********)
Lemma r_stric_increasing :
 forall h1 h2 : TypeSpeed, (h1 < h2)%R -> (r h1 < r h2)%R.
intros; unfold r in |- *; generalize (rho_strict_decreasing h1 h2 H);
 intro H0;
 generalize
  (Rinv_lt_contravar (rho h2) (rho h1)
     (Rmult_lt_0_compat (rho h2) (rho h1) (rho_pos h2) (rho_pos h1)) H0);
 intro;
 apply
  (Rmult_le_0_lt_compat h1 h2 (/ rho h1) (/ rho h2)
     (Rlt_le 0 h1 (TypeSpeed_pos h1))
     (Rlt_le 0 (/ rho h1) (Rinv_0_lt_compat (rho h1) (rho_pos h1))) H H1).
Qed.
