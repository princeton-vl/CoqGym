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


Section ycngftys.

Require Import Reals.
Require Import trajectory_const.
Require Import rrho.
Require Import trajectory_def.
Require Import constants.

Unset Standard Proposition Elimination Names.

Variable intr : Trajectory.

(**********)
Definition xi : R -> R := x intr.
Definition yi : R -> R := y intr.
Definition vi : TypeSpeed := h intr.
Definition xP (t : R) : R := (xi t - xi 0)%R.
Definition yP (t : R) : R := (yi t - yi 0)%R.
Definition u (eps : posreal) (t : R) : R :=
  sqrt (Rsqr (xP t) + Rsqr (yP t) + Rsqr eps).
Definition u0 (t : R) : R := sqrt (Rsqr (xP t) + Rsqr (yP t)).

(**********)
Lemma xi_derivable : derivable xi.
unfold xi in |- *; apply (cond_diff (x intr)).
Qed.

Lemma yi_derivable : derivable yi.
unfold yi in |- *; apply (cond_diff (y intr)).
Qed.

Lemma xP_derivable : derivable xP.
unfold xP in |- *.
reg; apply xi_derivable.
Qed.

Lemma yP_derivable : derivable yP.
unfold yP in |- *.
reg; apply yi_derivable.
Qed.

(**********)
Lemma d_u : forall eps : posreal, derivable (fun t : R => u eps t).
intro.
unfold u in |- *; unfold derivable in |- *; intro.
reg.
apply yP_derivable.
apply xP_derivable.
apply Rle_lt_trans with (Rsqr (xP x) + Rsqr (yP x))%R.
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
pattern (Rsqr (yP x)) at 1 in |- *; rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
apply Rsqr_pos_lt.
red in |- *; intro; assert (H0 := cond_pos eps); rewrite H in H0;
 elim (Rlt_irrefl _ H0).
Qed.

Lemma fct_der2 :
 forall (eps : posreal) (t : R), derivable_pt (fun y : R => Rsqr (u eps y)) t.
intros; set (f := u eps); reg.
apply (d_u eps).
Qed.

(**********)
Lemma D_Rsqr_u_epsilon_1 :
 forall (eps : posreal) (t : R),
 derive_pt (fun y : R => Rsqr (u eps y)) t (fct_der2 eps t) =
 (2 * u eps t * derive_pt (u eps) t (d_u eps t))%R. 
intros; set (f := u eps).
cut (derivable_pt f t); [ intro H | apply (d_u eps t) ].
cut (derive_pt f t H = derive_pt f t (d_u eps t)); [ intro | apply pr_nu ].
reg.
Qed.

(**********)
Lemma xP_derive :
 forall t : R,
 derive_pt xP t (xP_derivable t) = derive_pt xi t (xi_derivable t).
intro; unfold xP in |- *; reg.
apply pr_nu.
apply xi_derivable.
Qed.

Lemma yP_derive :
 forall t : R,
 derive_pt yP t (yP_derivable t) = derive_pt yi t (yi_derivable t).
intro; unfold yP in |- *; reg.
apply pr_nu.
apply yi_derivable.
Qed.

Lemma fct_der3 :
 forall (eps : posreal) (t : R),
 derivable_pt (fun y : R => (Rsqr (xP y) + (Rsqr (yP y) + Rsqr eps))%R) t.
intros; reg.
apply yP_derivable.
apply xP_derivable.
Qed.

(**********)
Lemma D_Rsqr_u_epsilon_2 :
 forall (eps : posreal) (t : R),
 (derive_pt (fun y : R => Rsqr (u eps y)) t (fct_der2 eps t) <= 2 * u0 t * vi)%R.
intros; set (f := u eps).
replace (derive_pt (fun y : R => Rsqr (f y)) t (fct_der2 eps t)) with
 (derive_pt (fun y : R => (Rsqr (xP y) + (Rsqr (yP y) + Rsqr eps))%R) t
    (fct_der3 eps t)).
replace
 (derive_pt (fun y : R => (Rsqr (xP y) + (Rsqr (yP y) + Rsqr eps))%R) t
    (fct_der3 eps t)) with
 (2 * derive_pt xP t (xP_derivable t) * xP t +
  2 * derive_pt yP t (yP_derivable t) * yP t)%R.
rewrite (xP_derive t).
rewrite (yP_derive t).
assert (H0 := cond_x intr t).
assert (H1 := cond_y intr t).
cut
 (derive_pt (x intr) t (cond_diff (x intr) t) =
  derive_pt xi t (xi_derivable t)); [ intro | apply pr_nu ].
cut
 (derive_pt (y intr) t (cond_diff (y intr) t) =
  derive_pt yi t (yi_derivable t)); [ intro | apply pr_nu ].
rewrite <- H; rewrite <- H2; rewrite H1; rewrite H0.
unfold vi in |- *.
repeat rewrite Rmult_assoc.
rewrite <- Rmult_plus_distr_l.
apply Rmult_le_compat_l.
left; prove_sup0.
rewrite <- Rmult_plus_distr_l.
rewrite (Rmult_comm (u0 t)); apply Rmult_le_compat_l.
left; apply (TypeSpeed_pos (h intr)).
generalize
 (sqrt_cauchy (cos (theta intr t)) (sin (theta intr t)) (xP t) (yP t));
 rewrite (Rplus_comm (Rsqr (cos (theta intr t)))); 
 rewrite sin2_cos2; rewrite sqrt_1; rewrite Rmult_1_l; 
 intro H8; unfold u0 in |- *; assumption.
set (H0 := xP_derivable t).
set (H1 := yP_derivable t).
symmetry  in |- *; reg.
unfold derive_pt in |- *; unfold derivable_pt_abs in |- *;
 cut
  (forall l : R,
   derivable_pt_lim (fun y : R => (Rsqr (xP y) + (Rsqr (yP y) + Rsqr eps))%R)
     t l <-> derivable_pt_lim (fun y : R => Rsqr (f y)) t l).
intro; unfold projT1 in |- *.
case (fct_der3 eps t); intros.
case (fct_der2 eps t); intros.
assert (H0 := H x).
unfold derivable_pt_abs in d.
elim H0; intros; fold f in d0.
assert (H3 := H1 d).
eapply uniqueness_limite.
apply H3.
apply d0.
intro; unfold derivable_pt_lim in |- *.
split; intros.
elim (H eps0 H0); intros.
exists x; intros; unfold f in |- *; unfold u in |- *.
repeat rewrite Rsqr_sqrt.
repeat rewrite Rplus_assoc.
apply H1; assumption.
repeat apply Rplus_le_le_0_compat; try apply Rle_0_sqr.
repeat apply Rplus_le_le_0_compat; try apply Rle_0_sqr.
elim (H eps0 H0); intros.
exists x; intros; unfold f in H1; unfold u in H1.
replace
 ((Rsqr (xP (t + h)) + (Rsqr (yP (t + h)) + Rsqr eps) -
   (Rsqr (xP t) + (Rsqr (yP t) + Rsqr eps))) / h - l)%R with
 ((Rsqr (sqrt (Rsqr (xP (t + h)) + Rsqr (yP (t + h)) + Rsqr eps)) -
   Rsqr (sqrt (Rsqr (xP t) + Rsqr (yP t) + Rsqr eps))) / h - l)%R.
apply H1; assumption.
repeat rewrite Rsqr_sqrt.
repeat rewrite Rplus_assoc; reflexivity.
repeat apply Rplus_le_le_0_compat; try apply Rle_0_sqr.
repeat apply Rplus_le_le_0_compat; try apply Rle_0_sqr.
Qed.

(**********)
Lemma u_stric_pos : forall (eps : posreal) (t : R), (0 < u eps t)%R.
intros; unfold u in |- *; apply sqrt_lt_R0; apply Rplus_le_lt_0_compat;
 [ apply Rplus_le_le_0_compat; apply Rle_0_sqr
 | apply Rsqr_pos_lt; red in |- *; intro H; generalize (cond_pos eps);
    intro H0; rewrite H in H0; elim (Rlt_irrefl 0 H0) ].
Qed.

Lemma u_pos : forall (eps : posreal) (t : R), (0 <= u eps t)%R.
intros; left; apply u_stric_pos.
Qed.

Lemma u0_pos : forall t : R, (0 <= u0 t)%R.
intros; unfold u0 in |- *; apply sqrt_positivity; apply Rplus_le_le_0_compat;
 apply Rle_0_sqr.
Qed.

(**********)
Lemma Rsqr_u_epsilon :
 forall (eps : posreal) (t : R), Rsqr (u eps t) = (Rsqr (u0 t) + Rsqr eps)%R.
intros; apply sqrt_inj;
 [ apply Rle_0_sqr
 | apply Rplus_le_le_0_compat; apply Rle_0_sqr
 | rewrite sqrt_Rsqr;
    [ unfold u0 in |- *; rewrite Rsqr_sqrt;
       [ unfold u in |- *; reflexivity
       | apply Rplus_le_le_0_compat; apply Rle_0_sqr ]
    | apply (u_pos eps t) ] ].
Qed.

(**********)
Lemma u0_u_epsilon : forall (eps : posreal) (t : R), (u0 t <= u eps t)%R.
intros; apply Rsqr_incr_0;
 [ unfold u0, u in |- *; repeat rewrite Rsqr_sqrt;
    [ rewrite <- (Rplus_0_r (Rsqr (xP t) + Rsqr (yP t)));
       repeat rewrite Rplus_assoc; repeat apply Rplus_le_compat_l;
       rewrite Rplus_0_l; apply Rle_0_sqr
    | repeat apply Rplus_le_le_0_compat; apply Rle_0_sqr
    | apply Rplus_le_le_0_compat; apply Rle_0_sqr ]
 | apply u0_pos
 | apply u_pos ].
Qed.

(**********)
Lemma u_epsilon_le_v :
 forall (eps : posreal) (t : R), (derive_pt (u eps) t (d_u eps t) <= vi)%R.
intros.
generalize (D_Rsqr_u_epsilon_2 eps t); intro H.
rewrite (D_Rsqr_u_epsilon_1 eps t) in H.
repeat rewrite Rmult_assoc in H.
assert (Hyp : (0 < 2)%R).
prove_sup0.
generalize
 (Rmult_le_reg_l 2 (u eps t * derive_pt (u eps) t (d_u eps t)) 
    (u0 t * vi) Hyp H); intro H1.
generalize (u0_u_epsilon eps t); intro H2;
 generalize
  (Rmult_le_compat_r (v vi) (u0 t) (u eps t) (Rlt_le 0 vi (TypeSpeed_pos vi))
     H2); intro H3.
generalize
 (Rle_trans (u eps t * derive_pt (u eps) t (d_u eps t)) 
    (u0 t * vi) (u eps t * vi) H1 H3); intro H4.
apply
 (Rmult_le_reg_l (u eps t) (derive_pt (u eps) t (d_u eps t)) vi
    (u_stric_pos eps t) H4).
Qed.

(**********)
Lemma vit_derivable : derivable (fun t : R => (vi * t)%R).
reg.
Qed.

Lemma derive_vit :
 forall t : R, derive_pt (fun t : R => (vi * t)%R) t (vit_derivable t) = vi.
intro; reg.
Qed.

(**********)
Lemma u_epsilon_le_vt :
 forall (eps : posreal) (t : R), (0 <= t)%R -> (u eps t - eps <= vi * t)%R.
intros.
generalize
 (IAF_var (fun t : R => (vi * t)%R) (fun t : R => u eps t) 0 t vit_derivable
    (d_u eps) H); intros.
cut (u eps 0 = eps).
intro H1.
rewrite <- H1.
elim H0; intros.
rewrite Rmult_0_r in H2; unfold Rminus in H2; rewrite Ropp_0 in H2;
 rewrite Rplus_0_r in H2; left; assumption.
rewrite Rmult_0_r in H2; unfold Rminus in H2; rewrite Ropp_0 in H2;
 rewrite Rplus_0_r in H2; right; assumption.
rewrite (derive_vit c); apply (u_epsilon_le_v eps c).
unfold u in |- *; unfold xP in |- *; unfold yP in |- *; unfold Rminus in |- *;
 repeat rewrite Rplus_opp_r; rewrite Rsqr_0; repeat rewrite Rplus_0_l;
 apply (sqrt_Rsqr eps (Rlt_le 0 eps (cond_pos eps))).
Qed.

(**********)
Lemma Rsqr_u :
 forall (eps : posreal) (t : R),
 (0 <= t)%R -> (Rsqr (u0 t) <= Rsqr vi * Rsqr t + 2 * eps * vi * t)%R.
intros; cut (u eps t <= vi * t + eps)%R.
intro H0; generalize (u_pos eps t); intro H1;
 generalize
  (Rsqr_incr_1 (u eps t) (vi * t + eps) H0 H1
     (Rle_trans 0 (u eps t) (vi * t + eps) H1 H0)); 
 intro H2; rewrite Rsqr_plus in H2; rewrite Rsqr_u_epsilon in H2;
 rewrite Rsqr_mult in H2; rewrite <- (Rplus_comm (2 * (vi * t) * eps)) in H2;
 generalize
  (Rplus_le_compat_r (- Rsqr eps) (Rsqr (u0 t) + Rsqr eps)
     (2 * (vi * t) * eps + (Rsqr vi * Rsqr t + Rsqr eps)) H2);
 unfold Rminus in |- *; repeat rewrite Rplus_assoc;
 repeat rewrite Rplus_opp_r; repeat rewrite Rplus_0_r; 
 intro H3;
 replace (Rsqr vi * Rsqr t + 2 * eps * vi * t)%R with
  (2 * (vi * t) * eps + Rsqr vi * Rsqr t)%R.
assumption.
ring.
apply Rplus_le_reg_l with (- eps)%R; rewrite Rplus_comm;
 replace (- eps + (vi * t + eps))%R with (vi * t)%R.
generalize (u_epsilon_le_vt eps t H); unfold Rminus in |- *; intro;
 assumption.
ring.
Qed.

(**********)
Lemma Rsqr_u_Rsqr_vt :
 forall (eps : posreal) (t : R),
 (0 <= t)%R -> (Rsqr (u0 t) <= Rsqr vi * Rsqr t + eps)%R.
intros; case (Rtotal_order 0 t); intro.
cut (0 < eps / (2 * vi * t))%R.
intro; generalize (Rsqr_u (mkposreal (eps / (2 * vi * t)) H1) t H);
 simpl in |- *;
 replace (2 * (eps / (2 * vi * t)) * vi * t)%R with (eps * 1)%R.
rewrite Rmult_1_r; intro; assumption.
unfold Rdiv in |- *; repeat rewrite Rinv_mult_distr.
replace (2 * (eps * (/ 2 * / vi * / t)) * vi * t)%R with
 (eps * (2 * / 2) * (/ vi * vi) * (/ t * t))%R.
repeat rewrite <- Rinv_l_sym.
rewrite <- Rinv_r_sym.
repeat rewrite Rmult_1_r; reflexivity.
discrR.
red in |- *; intro H2; rewrite H2 in H0; elim (Rlt_irrefl 0 H0).
generalize (TypeSpeed_pos vi); intro H2; red in |- *; intro H3;
 rewrite H3 in H2; elim (Rlt_irrefl 0 H2).
ring.
discrR.
generalize (TypeSpeed_pos vi); intro H2; red in |- *; intro H3;
 rewrite H3 in H2; elim (Rlt_irrefl 0 H2).
apply prod_neq_R0.
discrR.
generalize (TypeSpeed_pos vi); intro H2; red in |- *; intro H3;
 rewrite H3 in H2; elim (Rlt_irrefl 0 H2).
red in |- *; intro H2; rewrite H2 in H0; elim (Rlt_irrefl 0 H0).
unfold Rdiv in |- *; apply Rmult_lt_0_compat.
apply (cond_pos eps).
apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat.
prove_sup0.
apply (TypeSpeed_pos vi).
assumption.
elim H0; intro.
rewrite <- H1; unfold u0 in |- *; unfold xP, yP in |- *;
 unfold Rminus in |- *; repeat rewrite Rplus_opp_r; 
 repeat rewrite Rsqr_0; rewrite Rmult_0_r; repeat rewrite Rplus_0_l;
 rewrite sqrt_0; rewrite Rsqr_0; left; apply (cond_pos eps).
elim (Rlt_irrefl 0 (Rle_lt_trans 0 t 0 H H1)).
Qed.

(**********************)
(****** THEOREM *******)
(**********************)

Theorem YCNGFTYS :
 forall t : R,
 (0 <= t)%R -> (sqrt (Rsqr (xi t - xi 0) + Rsqr (yi t - yi 0)) <= v vi * t)%R.
intros; apply Rsqr_incr_0.
rewrite Rsqr_mult; apply le_epsilon; intros;
 generalize (Rsqr_u_Rsqr_vt (mkposreal eps H0) t H); 
 simpl in |- *; unfold u0 in |- *; unfold xP, yP in |- *; 
 intro H1; assumption.
apply sqrt_positivity; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
apply Rmult_le_pos; [ left; apply (TypeSpeed_pos vi) | assumption ].
Qed.

End ycngftys.
