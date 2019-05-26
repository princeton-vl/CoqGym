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


Section trajectory.

Require Import Bool.
Require Import Reals.
Require Import trajectory_const.
Require Import rrho.
Require Import trajectory_def.
Require Import constants.
Require Import ycngftys.
Require Import ycngstys.
Require Import Omega.

Unset Standard Proposition Elimination Names.

Variable intr : Trajectory.
Variable evad : EvaderTrajectory.
Variable T : TimeT.

Lemma thetat_derivable : derivable (thetat intr).
unfold thetat in |- *; apply (cond_diff (theta intr)).
Qed.

Definition xe : R := x (tr evad) T.
Definition ye : R := y (tr evad) T.
Definition ve : R := v (h (tr evad)).
Definition r_vi : R := r (vi intr).
Definition rho_vi : R := rho (vi intr).
Definition Die (ti te : R) : R :=
  sqrt
    (Rsqr (xi intr ti - x (tr evad) te) + Rsqr (yi intr ti - y (tr evad) te)).
Definition conflict (t : R) : bool :=
  match Rle_dec (Die t t) ConflictRange with
  | left _ => true
  | right _ => false
  end.


Lemma Dx :
 forall t : R,
 derive_pt (xi intr) t (xi_derivable intr t) =
 (vi intr * cos (thetat intr t))%R.
intro; unfold xi, vi, thetat in |- *.
assert (H := cond_x intr t).
rewrite <- H.
apply pr_nu.
Qed.


Lemma Dy :
 forall t : R,
 derive_pt (yi intr) t (yi_derivable intr t) =
 (vi intr * sin (thetat intr t))%R.
intro; unfold yi, vi, thetat in |- *.
assert (H := cond_y intr t).
rewrite <- H.
apply pr_nu.
Qed.

(* Easy to prove with constructive reals *)
Axiom r_sin_rho : (ConflictRange < r_vi * sin rho_vi)%R.

Definition l : R := Die 0 T.
Definition d : R := Die 0 0.

Axiom
  beta_exists :
    { beta : R |
       xe = (l * cos beta + xi intr 0)%R /\
       ye = (yi intr 0 - l * sin beta)%R /\
       (0 <= beta + thetat intr 0 < 2 * PI)%R }.

Definition beta := let (a,_) := beta_exists in a.

Lemma beta_def :
 xe = (l * cos beta + xi intr 0)%R /\
 ye = (yi intr 0 - l * sin beta)%R /\ (0 <= beta + thetat intr 0 < 2 * PI)%R.
unfold beta in |- *; case beta_exists; trivial.
Qed.

Definition Omega (a : R) : bool :=
  match Rle_dec (PI / 2) a with
  | left _ =>
      match Rle_dec a (3 * (PI / 2)) with
      | left _ => true
      | right _ => false
      end
  | right _ => false
  end.

Lemma xe_0 : xe = (l * cos beta + xi intr 0)%R.
Proof with trivial.
generalize beta_def; intro; elim H...
Qed.

Lemma ye_0 : ye = (yi intr 0 - l * sin beta)%R.
Proof with trivial.
generalize beta_def; intro; elim H; intros _ H0; elim H0...
Qed.

Lemma d_l_beta :
 Rsqr d = (Rsqr (ve * T) + Rsqr l - 2 * ve * T * l * cos beta)%R.
Proof with trivial.
unfold d in |- *; unfold Die in |- *; rewrite Rsqr_sqrt...
replace (xi intr 0 - x (tr evad) 0)%R with
 (xi intr 0 - xe + (xe - x (tr evad) 0))%R...
replace (yi intr 0 - y (tr evad) 0)%R with
 (yi intr 0 - ye + (ye - y (tr evad) 0))%R...
repeat rewrite Rsqr_plus; cut ((ye - y (tr evad) 0)%R = 0%R)...
intro; rewrite H; repeat rewrite Rmult_0_r; rewrite Rsqr_0;
 repeat rewrite Rplus_0_r; cut ((xe - x (tr evad) 0)%R = (ve * T)%R)...
intro; rewrite H0;
 replace
  (Rsqr (xi intr 0 - xe) + Rsqr (ve * T) + 2 * (xi intr 0 - xe) * (ve * T) +
   Rsqr (yi intr 0 - ye))%R with
  (Rsqr (ve * T) + (Rsqr (xi intr 0 - xe) + Rsqr (yi intr 0 - ye)) +
   2 * (xi intr 0 - xe) * (ve * T))%R...
cut (Rsqr l = (Rsqr (xi intr 0 - xe) + Rsqr (yi intr 0 - ye))%R)...
intro; rewrite <- H1; rewrite xe_0; ring...
unfold l in |- *; unfold Die in |- *; rewrite Rsqr_sqrt;
 [ unfold xe, ye in |- * | apply Rplus_le_le_0_compat; apply Rle_0_sqr ]...
ring...
unfold xe, ve in |- *; rewrite (tr_cond1 evad); ring...
unfold ye, ve in |- *; rewrite (tr_cond2 evad); unfold Rminus in |- *;
 rewrite Rplus_opp_r...
ring...
ring...
apply Rplus_le_le_0_compat; apply Rle_0_sqr...
Qed.

Definition yp (t : R) : R :=
  (- sin (thetat intr 0) * (xi intr t - xe) +
   cos (thetat intr 0) * (yi intr t - ye))%R.

Hint Resolve xi_derivable yi_derivable: diff.

Lemma yp_derivable : derivable yp.
unfold yp in |- *; set (thetat_p := thetat intr); set (xi_p := xi intr);
 set (yi_p := yi intr); reg.
apply (yi_derivable intr).
apply (xi_derivable intr).
Qed.
Hint Resolve yp_derivable: diff.

Definition xp (t : R) : R :=
  (cos (thetat intr 0) * (xi intr t - xe) +
   sin (thetat intr 0) * (yi intr t - ye))%R.

Lemma xp_derivable : derivable xp.
unfold xp in |- *; set (thetat_p := thetat intr); set (xi_p := xi intr);
 set (yi_p := yi intr); reg.
apply (yi_derivable intr).
apply (xi_derivable intr).
Qed.
Hint Resolve xp_derivable: diff.

Definition Rsqr_evader_distance (t : R) : R :=
  (Rsqr (xi intr t - xe) + Rsqr (yi intr t - ye))%R.

Lemma Rsqr_evader_distance_derivable : derivable Rsqr_evader_distance.
unfold Rsqr_evader_distance in |- *.
set (xi_p := xi intr); set (yi_p := yi intr); reg. 
apply (yi_derivable intr).
apply (xi_derivable intr).
Qed.
Hint Resolve Rsqr_evader_distance_derivable: diff.

Definition Rsqr_intruder_distance (t : R) : R :=
  (Rsqr (xi intr t - xi intr 0) + Rsqr (yi intr t - yi intr 0))%R.

Lemma Rsqr_intruder_distance_derivable : derivable Rsqr_intruder_distance.
unfold Rsqr_intruder_distance in |- *; set (xi_p := xi intr);
 set (yi_p := yi intr); reg.
apply (yi_derivable intr).
apply (xi_derivable intr).
Qed.
Hint Resolve Rsqr_intruder_distance_derivable: diff.

Lemma Rsqr_evader_distance_pos :
 forall t : R, (0 <= Rsqr_evader_distance t)%R.
intro; unfold Rsqr_evader_distance in |- *; apply Rplus_le_le_0_compat;
 apply Rle_0_sqr.
Qed.

Lemma Rsqr_intruder_distance_pos :
 forall t : R, (0 <= Rsqr_intruder_distance t)%R.
intro; unfold Rsqr_intruder_distance in |- *; apply Rplus_le_le_0_compat;
 apply Rle_0_sqr.
Qed.

Definition e (t : R) : R := sqrt (Rsqr_evader_distance t).
Definition i (t : R) : R := sqrt (Rsqr_intruder_distance t).

Lemma conflict_T_e_0 : conflict T = true -> (e T <= ConflictRange)%R. 
Proof with trivial.
unfold conflict in |- *; cut (e T = Die T T)...
intro; case (Rle_dec (Die T T) ConflictRange); intros;
 [ rewrite H; exact r | elim diff_false_true ]...
Qed.

Lemma conflict_T_e_1 : (e T <= ConflictRange)%R -> conflict T = true.
Proof with trivial.
intro; cut (e T = Die T T)...
intro; rewrite H0 in H; unfold conflict in |- *;
 case (Rle_dec (Die T T) ConflictRange); intro...
elim n; assumption...
Qed.

Lemma L : Rsqr l = (Rsqr (xe - xi intr 0) + Rsqr (ye - yi intr 0))%R.
rewrite xe_0; rewrite ye_0; unfold Rminus in |- *;
 rewrite <- (Rplus_comm (- (l * sin beta))); repeat rewrite Rplus_assoc;
 repeat rewrite Rplus_opp_r; repeat rewrite Rplus_0_r; 
 rewrite <- Rsqr_neg; repeat rewrite Rsqr_mult;
 rewrite <- (Rmult_comm (Rsqr (sin beta))); rewrite sin2;
 unfold Rminus in |- *; rewrite Rmult_plus_distr_r; 
 ring.
Qed.

Lemma L_intruder : forall t : R, (l <= e t + i t)%R.
intro; apply Rsqr_incr_0.
rewrite Rsqr_plus.
cut
 (Rsqr l =
  (Rsqr (e t) + Rsqr (i t) +
   2 *
   ((xe - xi intr t) * (xi intr t - xi intr 0) +
    (ye - yi intr t) * (yi intr t - yi intr 0)))%R).
intro.
rewrite H.
apply Rplus_le_compat_l.
repeat rewrite Rmult_assoc.
apply Rmult_le_compat_l.
left; prove_sup0.
unfold e, i in |- *.
unfold Rsqr_evader_distance, Rsqr_intruder_distance in |- *.
rewrite (Rsqr_neg (xi intr t - xe)).
rewrite (Rsqr_neg (yi intr t - ye)).
replace (- (xi intr t - xe))%R with (xe - xi intr t)%R.
replace (- (yi intr t - ye))%R with (ye - yi intr t)%R.
apply sqrt_cauchy.
ring.
ring.
rewrite L.
unfold e, i in |- *.
repeat rewrite Rsqr_sqrt.
unfold Rsqr_evader_distance, Rsqr_intruder_distance in |- *.
replace (xe - xi intr 0)%R with (xe - xi intr t + (xi intr t - xi intr 0))%R.
replace (ye - yi intr 0)%R with (ye - yi intr t + (yi intr t - yi intr 0))%R.
repeat rewrite Rsqr_plus.
rewrite (Rsqr_neg (xe - xi intr t)).
rewrite (Rsqr_neg (ye - yi intr t)).
replace (- (xe - xi intr t))%R with (xi intr t - xe)%R.
replace (- (ye - yi intr t))%R with (yi intr t - ye)%R.
ring.
ring.
ring.
ring.
ring.
apply Rsqr_intruder_distance_pos.
apply Rsqr_evader_distance_pos.
unfold l in |- *; unfold Die in |- *.
apply sqrt_positivity.
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
unfold e, i in |- *; apply Rplus_le_le_0_compat; apply sqrt_positivity.
apply Rsqr_evader_distance_pos.
apply Rsqr_intruder_distance_pos.
Qed.

Lemma l_is_pos : (0 <= l)%R.
unfold l in |- *; unfold Die in |- *; apply sqrt_positivity;
 apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma L_e : forall t : R, (e t <= l + i t)%R.
intro.
apply Rsqr_incr_0.
rewrite Rsqr_plus.
cut
 (Rsqr (e t) =
  (Rsqr l + Rsqr (i t) +
   2 *
   ((xi intr t - xi intr 0) * (xi intr 0 - xe) +
    (yi intr t - yi intr 0) * (yi intr 0 - ye)))%R).
intro.
rewrite H.
apply Rplus_le_compat_l.
repeat rewrite Rmult_assoc.
apply Rmult_le_compat_l.
left; prove_sup0.
cut (l = sqrt (Rsqr (xe - xi intr 0) + Rsqr (ye - yi intr 0))).
intro.
rewrite H0.
unfold i in |- *.
unfold Rsqr_intruder_distance in |- *.
rewrite (Rsqr_neg (xe - xi intr 0)).
rewrite (Rsqr_neg (ye - yi intr 0)).
replace (- (xe - xi intr 0))%R with (xi intr 0 - xe)%R.
replace (- (ye - yi intr 0))%R with (yi intr 0 - ye)%R.
rewrite <-
 (Rmult_comm
    (sqrt (Rsqr (xi intr t - xi intr 0) + Rsqr (yi intr t - yi intr 0))))
 .
apply sqrt_cauchy.
ring.
ring.
apply Rsqr_inj.
apply l_is_pos.
apply sqrt_positivity; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
rewrite Rsqr_sqrt.
apply L.
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
rewrite L.
unfold e, i in |- *.
repeat rewrite Rsqr_sqrt.
unfold Rsqr_evader_distance, Rsqr_intruder_distance in |- *.
replace (xi intr t - xe)%R with (xi intr t - xi intr 0 + (xi intr 0 - xe))%R.
replace (yi intr t - ye)%R with (yi intr t - yi intr 0 + (yi intr 0 - ye))%R.
repeat rewrite Rsqr_plus.
rewrite (Rsqr_neg (xe - xi intr 0)).
rewrite (Rsqr_neg (ye - yi intr 0)).
replace (- (xe - xi intr 0))%R with (xi intr 0 - xe)%R.
replace (- (ye - yi intr 0))%R with (yi intr 0 - ye)%R.
ring.
ring.
ring.
ring.
ring.
apply Rsqr_intruder_distance_pos.
apply Rsqr_evader_distance_pos.
unfold e in |- *.
apply sqrt_positivity.
apply Rsqr_evader_distance_pos.
apply Rplus_le_le_0_compat.
apply l_is_pos.
unfold i in |- *.
apply sqrt_positivity.
apply Rsqr_intruder_distance_pos.
Qed.

Lemma L_i : forall t : R, (i t <= l + e t)%R.
intro.
apply Rsqr_incr_0.
rewrite Rsqr_plus.
cut
 (Rsqr (i t) =
  (Rsqr l + Rsqr (e t) +
   2 *
   ((xi intr t - xe) * (xe - xi intr 0) + (yi intr t - ye) * (ye - yi intr 0)))%R).
intro.
rewrite H.
apply Rplus_le_compat_l.
repeat rewrite Rmult_assoc.
apply Rmult_le_compat_l.
left; prove_sup0.
cut (l = sqrt (Rsqr (xe - xi intr 0) + Rsqr (ye - yi intr 0))).
intro.
rewrite H0.
unfold e in |- *.
unfold Rsqr_evader_distance in |- *.
rewrite <-
 (Rmult_comm (sqrt (Rsqr (xi intr t - xe) + Rsqr (yi intr t - ye))))
 .
apply sqrt_cauchy.
apply Rsqr_inj.
apply l_is_pos.
apply sqrt_positivity; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
rewrite Rsqr_sqrt.
apply L.
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
rewrite L.
unfold e, i in |- *.
repeat rewrite Rsqr_sqrt.
unfold Rsqr_evader_distance, Rsqr_intruder_distance in |- *.
replace (xi intr t - xi intr 0)%R with (xi intr t - xe + (xe - xi intr 0))%R.
replace (yi intr t - yi intr 0)%R with (yi intr t - ye + (ye - yi intr 0))%R.
repeat rewrite Rsqr_plus.
ring.
ring.
ring.
apply Rsqr_evader_distance_pos.
apply Rsqr_intruder_distance_pos.
unfold i in |- *.
apply sqrt_positivity.
apply Rsqr_intruder_distance_pos.
apply Rplus_le_le_0_compat.
apply l_is_pos.
unfold e in |- *.
apply sqrt_positivity.
apply Rsqr_evader_distance_pos.
Qed.

Lemma theta_inv :
 forall t : R,
 (0 <= t)%R ->
 (thetat intr 0 - rho_vi * t <= thetat intr t)%R /\
 (thetat intr t <= thetat intr 0 + rho_vi * t)%R.
Proof with trivial.
generalize (dtheta_rho intr); intros; split...
unfold thetat in |- *; cut (derivable (fun y : R => (- rho_vi * y)%R));
 [ intro X | reg ]...
cut
 (forall z : R,
  derive_pt (fun y : R => (- rho_vi * y)%R) z (X z) = (- rho_vi)%R);
 [ intro | intro; reg ]...
apply Rplus_le_reg_l with (- theta intr 0)%R...
replace (- theta intr 0 + (theta intr 0 - rho_vi * t))%R with
 (- rho_vi * t - - rho_vi * 0)%R; [ idtac | ring ]...
replace (- theta intr 0 + theta intr t)%R with
 (theta intr t - theta intr 0)%R; [ idtac | ring ]...
apply
 (IAF_var (theta intr) (fun y : R => (- rho_vi * y)%R) 0 t
    (cond_diff (theta intr)) X H0)...
intros; rewrite (H1 c); unfold rho_vi in |- *; unfold vi in |- *; elim (H c);
 intros H4 _; assumption...
unfold thetat in |- *; cut (derivable (fun y : R => (rho_vi * y)%R));
 [ intro X | reg ]...
cut (forall z : R, derive_pt (fun y : R => (rho_vi * y)%R) z (X z) = rho_vi);
 [ intro | intro; reg ]...
apply Rplus_le_reg_l with (- theta intr 0)%R...
replace (- theta intr 0 + (theta intr 0 + rho_vi * t))%R with
 (rho_vi * t - rho_vi * 0)%R; [ idtac | ring ]...
replace (- theta intr 0 + theta intr t)%R with
 (theta intr t - theta intr 0)%R; [ idtac | ring ]...
apply
 (IAF_var (fun y : R => (rho_vi * y)%R) (theta intr) 0 t X
    (cond_diff (theta intr)) H0)...
intros; rewrite (H1 c); unfold rho_vi in |- *; unfold vi in |- *; elim (H c)...
Qed.

Lemma rho_t_pos : forall t : R, (0 <= t)%R -> (0 <= rho_vi * t)%R.
Proof with trivial.
intros; apply Rmult_le_pos...
left; unfold rho_vi in |- *; apply rho_pos...
Qed.

Lemma rho_t_le :
 forall t1 t2 : R, (t1 <= t2)%R -> (rho_vi * t1 <= rho_vi * t2)%R.
Proof with trivial.
intros; apply Rmult_le_compat_l...
left; unfold rho_vi in |- *; apply rho_pos...
Qed.

Lemma Dyp :
 forall t : R,
 derive_pt yp t (yp_derivable t) =
 (v (vi intr) * sin (thetat intr t - thetat intr 0))%R.
intro; unfold yp in |- *.
assert (H := xi_derivable intr t).
assert (H0 := yi_derivable intr t).
assert (H1 := thetat_derivable t).
set (xi_p := xi intr) in H |- *.
set (yi_p := yi intr) in H0 |- *.
set (thetat_p := thetat intr) in H1 |- *.
reg.
assert (H2 := cond_x intr t).
assert (H3 := cond_y intr t).
replace (derive_pt xi_p t H) with
 (derive_pt (x intr) t (cond_diff (x intr) t)); [ idtac | apply pr_nu ].
replace (derive_pt yi_p t H0) with
 (derive_pt (y intr) t (cond_diff (y intr) t)); [ idtac | apply pr_nu ].
rewrite H2; rewrite H3.
rewrite sin_minus.
unfold fct_cte, vi, thetat_p, thetat in |- *.
ring.
Qed.

Lemma Dyp0_PI2 :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI / 2)%R ->
 (- (vi intr * sin (rho_vi * t)) <= derive_pt yp t (yp_derivable t) <=
  vi intr * sin (rho_vi * t))%R.
Proof with trivial.
intros...
rewrite Dyp...
generalize (theta_inv t H); intro; elim H1; intros...
cut (thetat intr t - thetat intr 0 <= rho_vi * t)%R...
cut (- (rho_vi * t) <= thetat intr t - thetat intr 0)%R...
intros...
split...
replace (- (vi intr * sin (rho_vi * t)))%R with
 (vi intr * - sin (rho_vi * t))%R...
apply Rmult_le_compat_l...
left; apply TypeSpeed_pos...
rewrite <- (sin_neg (rho_vi * t))...
apply sin_incr_1...
apply Ropp_ge_le_contravar; apply Rle_ge...
apply Rle_trans with 0%R...
rewrite <- Ropp_0...
apply Ropp_ge_le_contravar; apply Rle_ge; apply (rho_t_pos t H)...
left; apply PI2_RGT_0...
apply Rle_trans with (- (rho_vi * t))%R...
apply Ropp_ge_le_contravar...
apply Rle_ge...
apply Rle_trans with (rho_vi * t)%R...
ring...
apply Rmult_le_compat_l...
left; apply TypeSpeed_pos...
apply sin_incr_1...
apply Rle_trans with (- (rho_vi * t))%R...
apply Ropp_ge_le_contravar; apply Rle_ge...
apply Rle_trans with (rho_vi * t)%R...
apply Rle_trans with 0%R...
rewrite <- Ropp_0; apply Ropp_ge_le_contravar; apply Rle_ge; left;
 apply PI2_RGT_0...
apply (rho_t_pos t H)...
apply Rplus_le_reg_l with (thetat intr 0)...
unfold Rminus in |- *...
rewrite (Rplus_comm (thetat intr t))...
repeat rewrite <- Rplus_assoc...
rewrite Rplus_opp_r...
rewrite Rplus_0_l...
apply Rplus_le_reg_l with (thetat intr 0)...
unfold Rminus in |- *...
rewrite (Rplus_comm (thetat intr t))...
repeat rewrite <- Rplus_assoc...
rewrite Rplus_opp_r...
rewrite Rplus_0_l...
Qed.

Lemma yp0 : yp 0 = (l * sin (thetat intr 0 + beta))%R.
unfold yp in |- *; rewrite xe_0; rewrite ye_0;
 rewrite <- (Rplus_comm (xi intr 0)); unfold Rminus in |- *;
 repeat rewrite Ropp_plus_distr; repeat rewrite <- Rplus_assoc;
 repeat rewrite Rplus_opp_r; repeat rewrite Rplus_0_l; 
 rewrite sin_plus; ring.
Qed.

Definition hy (t : R) : R := (r_vi * cos (rho_vi * t))%R.

Lemma hy_derivable : derivable hy.
unfold hy in |- *; reg.
Qed.

Lemma Dhy :
 forall t : R,
 derive_pt hy t (hy_derivable t) = (- vi intr * sin (rho_vi * t))%R.
Proof with trivial.
intro; unfold hy in |- *; reg...
replace (vi intr:R) with (r_vi * rho_vi)%R.
ring.
unfold rho_vi, r_vi in |- *; unfold r in |- *.
field.
assert (H := rho_pos (vi intr)); red in |- *; intro; rewrite H0 in H;
 elim (Rlt_irrefl _ H)...
Qed.

Lemma ypt :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI / 2)%R -> (hy t - hy 0 <= yp t - yp 0 <= hy 0 - hy t)%R.
Proof with trivial.
intros; split...
apply (IAF_var yp hy 0 t yp_derivable hy_derivable H)...
intros; elim H1; intros...
generalize
 (Dyp0_PI2 c H2
    (Rle_trans (rho_vi * c) (rho_vi * t) (PI / 2) (rho_t_le c t H3) H0));
 intro...
elim H4; intros...
cut (derive_pt hy c (hy_derivable c) = (- (vi intr * sin (rho_vi * c)))%R)...
intro...
rewrite <- H7 in H5...
rewrite Dhy; ring...
replace (hy 0 - hy t)%R with ((- hy)%F t - (- hy)%F 0)%R...
apply
 (IAF_var (- hy)%F yp 0 t (derivable_opp hy hy_derivable) yp_derivable H)... 
intros; elim H1; intros...
generalize
 (Dyp0_PI2 c H2
    (Rle_trans (rho_vi * c) (rho_vi * t) (PI / 2) (rho_t_le c t H3) H0));
 intro...
elim H4; intros...
cut ((- derive_pt hy c (hy_derivable c))%R = (vi intr * sin (rho_vi * c))%R)...
intro; rewrite <- H7 in H6...
replace (derive_pt (- hy) c (derivable_opp hy hy_derivable c)) with
 (derive_pt (- hy) c (derivable_pt_opp hy c (hy_derivable c)));
 [ idtac | apply pr_nu ]...
rewrite (derive_pt_opp hy c (hy_derivable c))...
rewrite Dhy; ring...
unfold opp_fct in |- *; ring...
Qed.

Lemma ypt_PI2 :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI / 2)%R ->
 (l * sin (beta + thetat intr 0) + r_vi * (cos (rho_vi * t) - 1) <= yp t)%R /\
 (yp t <= l * sin (beta + thetat intr 0) - r_vi * (cos (rho_vi * t) - 1))%R.
intros; generalize (ypt t H H0); intro; elim H1; intros; split;
 [ unfold hy in H2; unfold Rminus in H2; rewrite yp0 in H2;
    rewrite Rmult_0_r in H2; rewrite cos_0 in H2; rewrite Rmult_1_r in H2;
    generalize
     (Rplus_le_compat_r (l * sin (thetat intr 0 + beta))
        (r_vi * cos (rho_vi * t) + - r_vi)
        (yp t + - (l * sin (thetat intr 0 + beta))) H2);
    replace (r_vi * cos (rho_vi * t) + - r_vi)%R with
     (r_vi * (cos (rho_vi * t) - 1))%R;
    [ repeat rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
       intro; rewrite <- (Rplus_comm (r_vi * (cos (rho_vi * t) - 1)));
       rewrite (Rplus_comm beta); assumption
    | ring ]
 | unfold hy in H3; unfold Rminus in H3; rewrite yp0 in H3;
    rewrite Rmult_0_r in H3; rewrite cos_0 in H3; rewrite Rmult_1_r in H3;
    generalize
     (Rplus_le_compat_r (l * sin (thetat intr 0 + beta))
        (yp t + - (l * sin (thetat intr 0 + beta)))
        (r_vi + - (r_vi * cos (rho_vi * t))) H3);
    replace (r_vi + - (r_vi * cos (rho_vi * t)))%R with
     (- (r_vi * (cos (rho_vi * t) - 1)))%R;
    [ repeat rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
       intro; unfold Rminus in |- *; rewrite (Rplus_comm beta);
       rewrite <- (Rplus_comm (- (r_vi * (cos (rho_vi * t) + -1))));
       assumption
    | unfold Rminus in |- *; rewrite Rmult_plus_distr_l; ring ] ].
Qed.


Lemma Dxp :
 forall t : R,
 derive_pt xp t (xp_derivable t) =
 (vi intr * cos (thetat intr t - thetat intr 0))%R.
intro; unfold xp in |- *.
assert (H := xi_derivable intr t).
assert (H0 := yi_derivable intr t).
assert (H1 := thetat_derivable t).
set (xi_p := xi intr) in H |- *.
set (yi_p := yi intr) in H0 |- *.
set (thetat_p := thetat intr) in H1 |- *.
reg.
assert (H2 := cond_x intr t).
assert (H3 := cond_y intr t).
replace (derive_pt yi_p t H0) with
 (derive_pt (y intr) t (cond_diff (y intr) t)); [ idtac | apply pr_nu ].
replace (derive_pt xi_p t H) with
 (derive_pt (x intr) t (cond_diff (x intr) t)); [ idtac | apply pr_nu ].
unfold vi in |- *.
rewrite H2; rewrite H3; rewrite cos_minus; unfold thetat_p, thetat; ring.
Qed.

Lemma Dx0_PI :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI)%R ->
 (vi intr * cos (rho_vi * t) <= derive_pt xp t (xp_derivable t))%R.
intros; rewrite Dxp; apply Rmult_le_compat_l;
 [ left; apply TypeSpeed_pos
 | generalize (theta_inv t H); intro; elim H1; intros;
    case (Rcase_abs (thetat intr t - thetat intr 0)); 
    intro;
    [ cut (thetat intr 0 - thetat intr t <= rho_vi * t)%R;
       [ cut (- (rho_vi * t) <= thetat intr 0 - thetat intr t)%R;
          [ intros; rewrite <- (cos_neg (thetat intr t - thetat intr 0));
             replace (- (thetat intr t - thetat intr 0))%R with
              (thetat intr 0 - thetat intr t)%R;
             [ apply cos_decr_1;
                [ left;
                   generalize
                    (Ropp_lt_gt_contravar (thetat intr t - thetat intr 0) 0 r);
                   rewrite Ropp_0;
                   replace (- (thetat intr t - thetat intr 0))%R with
                    (thetat intr 0 - thetat intr t)%R;
                   [ intro; assumption | ring ]
                | apply Rle_trans with (rho_vi * t)%R; assumption
                | apply (rho_t_pos t H)
                | assumption
                | assumption ]
             | ring ]
          | apply Rplus_le_reg_l with (thetat intr t + rho_vi * t)%R;
             repeat rewrite Rplus_assoc; rewrite Rplus_opp_r;
             rewrite Rplus_0_r;
             replace
              (thetat intr t + (rho_vi * t + (thetat intr 0 - thetat intr t)))%R
              with (thetat intr 0 + rho_vi * t)%R; 
             [ assumption | ring ] ]
       | apply Rplus_le_reg_l with (thetat intr t - rho_vi * t)%R;
          unfold Rminus in |- *; repeat rewrite Rplus_assoc;
          rewrite Rplus_opp_l; rewrite Rplus_0_r; rewrite Rplus_comm;
          repeat rewrite Rplus_assoc; rewrite Rplus_opp_l; 
          rewrite Rplus_0_r; rewrite Rplus_comm; assumption ]
    | generalize (Rge_le (thetat intr t - thetat intr 0) 0 r); intro;
       cut (thetat intr t - thetat intr 0 <= rho_vi * t)%R;
       [ cut (- (rho_vi * t) <= thetat intr t - thetat intr 0)%R;
          [ intros; apply cos_decr_1;
             [ assumption
             | apply Rle_trans with (rho_vi * t)%R; assumption
             | apply (rho_t_pos t H)
             | assumption
             | assumption ]
          | apply Rplus_le_reg_l with (thetat intr 0); unfold Rminus in |- *;
             rewrite (Rplus_comm (thetat intr t));
             repeat rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
             rewrite Rplus_0_l; assumption ]
       | apply Rplus_le_reg_l with (thetat intr 0); unfold Rminus in |- *;
          rewrite (Rplus_comm (thetat intr t)); repeat rewrite <- Rplus_assoc;
          rewrite Rplus_opp_r; rewrite Rplus_0_l; assumption ] ] ].
Qed.

Lemma xp0 : xp 0 = (- l * cos (thetat intr 0 + beta))%R.
unfold xp in |- *; rewrite xe_0; rewrite ye_0;
 rewrite <- (Rplus_comm (xi intr 0)); unfold Rminus in |- *;
 repeat rewrite Ropp_plus_distr; repeat rewrite <- Rplus_assoc;
 repeat rewrite Rplus_opp_r; repeat rewrite Rplus_0_l; 
 rewrite cos_plus; ring.
Qed.

Definition hx (t : R) : R := (r_vi * sin (rho_vi * t))%R.

Lemma hx_derivable : derivable hx.
unfold hx in |- *; reg.
Qed.

Lemma Dhx :
 forall t : R,
 derive_pt hx t (hx_derivable t) = (vi intr * cos (rho_vi * t))%R.
Proof with trivial.
intro; unfold hx in |- *; reg...
replace (vi intr:R) with (r_vi * rho_vi)%R.
ring.
unfold rho_vi, r_vi in |- *; unfold r in |- *.
field.
assert (H := rho_pos (vi intr)); red in |- *; intro; rewrite H0 in H;
 elim (Rlt_irrefl _ H)...
Qed.

Lemma xpt :
 forall t : R, (0 <= t)%R -> (rho_vi * t <= PI)%R -> (hx t <= xp t - xp 0)%R.
intros; replace (hx t) with (hx t - hx 0)%R.
apply (IAF_var xp hx 0 t xp_derivable hx_derivable H); intros; rewrite Dhx;
 elim H1; intros;
 apply
  (Dx0_PI c H2 (Rle_trans (rho_vi * c) (rho_vi * t) PI (rho_t_le c t H3) H0)). 
unfold hx in |- *; rewrite Rmult_0_r; rewrite sin_0; unfold Rminus in |- *;
 rewrite Rmult_0_r; rewrite Ropp_0; apply Rplus_0_r.
Qed.

Lemma r_sin_pos :
 forall t : R,
 (0 <= t)%R -> (rho_vi * t <= PI)%R -> (0 <= r_vi * sin (rho_vi * t))%R.
intros; apply Rmult_le_pos;
 [ left; unfold r_vi in |- *; unfold r in |- *; unfold Rdiv in |- *;
    apply Rmult_lt_0_compat;
    [ apply (TypeSpeed_pos (vi intr))
    | apply Rinv_0_lt_compat; apply (rho_pos (vi intr)) ]
 | apply sin_ge_0; [ apply (rho_t_pos t H) | assumption ] ].
Qed.

Lemma xpt_pos :
 forall t : R, (0 <= t)%R -> (rho_vi * t <= PI)%R -> (0 <= xp t - xp 0)%R.
intros; generalize (xpt t H H0); unfold hx in |- *; intro;
 apply Rle_trans with (r_vi * sin (rho_vi * t))%R;
 [ apply (r_sin_pos t H H0) | assumption ].
Qed.

Lemma xpt_PI :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI)%R ->
 (r_vi * sin (rho_vi * t) - l * cos (beta + thetat intr 0) <= xp t)%R.
intros; generalize (xpt t H H0); intro; unfold Rminus, hx in H1;
 rewrite xp0 in H1;
 generalize
  (Rplus_le_compat_l (- l * cos (thetat intr 0 + beta))
     (r_vi * sin (rho_vi * t)) (xp t + - (- l * cos (thetat intr 0 + beta)))
     H1); rewrite <- (Rplus_comm (r_vi * sin (rho_vi * t)));
 rewrite (Rplus_comm (- l * cos (thetat intr 0 + beta)));
 repeat rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
 rewrite (Rplus_comm beta); unfold Rminus in |- *; 
 intro;
 replace (- (l * cos (thetat intr 0 + beta)))%R with
  (- l * cos (thetat intr 0 + beta))%R; [ assumption | ring ].
Qed.

Lemma Omega_defeq :
 forall x : R, Omega x = true -> (PI / 2 <= x <= 3 * (PI / 2))%R.
Proof with trivial.
intro x; unfold Omega in |- *...
case (Rle_dec (PI / 2) x); intro...
case (Rle_dec x (3 * (PI / 2))); intros...
split...
elim diff_false_true...
intro; elim diff_false_true...
Qed.

Lemma neg_cos_var : forall x : R, cos (x - PI) = (- cos x)%R.
intro; rewrite cos_minus; rewrite cos_PI; rewrite sin_PI; ring.
Qed.

Lemma xp0_pos : Omega (beta + thetat intr 0) = true -> (0 <= xp 0)%R.
Proof with trivial.
intro; generalize (Omega_defeq (beta + thetat intr 0) H); intro; rewrite xp0;
 replace (- l * cos (thetat intr 0 + beta))%R with
  (l * - cos (thetat intr 0 + beta))%R...
apply Rmult_le_pos...
apply l_is_pos...
rewrite <- neg_cos_var; unfold Rminus in |- *; elim H0; intros;
 apply cos_ge_0...
apply Rplus_le_reg_l with PI; replace (PI + - (PI / 2))%R with (PI / 2)%R...
rewrite (Rplus_comm PI); repeat rewrite Rplus_assoc; rewrite Rplus_opp_l;
 rewrite Rplus_0_r; rewrite <- (Rplus_comm beta)...
pattern PI at 2 in |- *; rewrite double_var; ring... 
apply Rplus_le_reg_l with PI; replace (PI + PI / 2)%R with (3 * (PI / 2))%R...
rewrite (Rplus_comm PI); repeat rewrite Rplus_assoc; rewrite Rplus_opp_l;
 rewrite Rplus_0_r; rewrite <- (Rplus_comm beta)...
pattern PI at 2 in |- *; rewrite double_var; ring... 
ring...
Qed.

Lemma xpt_Omega :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI)%R ->
 Omega (beta + thetat intr 0) = true -> (r_vi * sin (rho_vi * t) <= xp t)%R.
intros; generalize (xpt t H H0); intro; generalize (xp0_pos H1); intro;
 unfold hx in H2;
 generalize
  (Rplus_le_compat_r (xp 0) (r_vi * sin (rho_vi * t)) (xp t - xp 0) H2);
 unfold Rminus in |- *; repeat rewrite Rplus_assoc; 
 rewrite Rplus_opp_l; rewrite Rplus_0_r; intro;
 apply (plus_le_is_le (r_vi * sin (rho_vi * t)) (xp 0) (xp t) H3 H4).
Qed.

Lemma isometric_evader :
 forall t : R, Rsqr_evader_distance t = (Rsqr (xp t) + Rsqr (yp t))%R.
intro; unfold Rsqr_evader_distance, xp, yp in |- *; repeat rewrite Rsqr_plus;
 ring_simplify; repeat rewrite Rsqr_mult;
 rewrite <- (Rsqr_neg (sin (thetat intr 0)));
 pattern (Rsqr (xi intr t - xe)) at 1 in |- *.
 replace (Rsqr (xi intr t - xe)) with
 ((Rsqr (sin (thetat intr 0)) + Rsqr (cos (thetat intr 0))) *
  Rsqr (xi intr t - xe))%R.
 pattern (Rsqr (yi intr t - ye)) at 1 in |- *.
 replace (Rsqr (yi intr t - ye)) with
  ((Rsqr (sin (thetat intr 0)) + Rsqr (cos (thetat intr 0))) *
   Rsqr (yi intr t - ye))%R.
 ring.
 rewrite sin2_cos2 in |- *;  ring.
 rewrite sin2_cos2 in |- *;  ring.
Qed.

Lemma xpt_xp0 :
 forall t : R,
 (xp t - xp 0)%R =
 (cos (thetat intr 0) * (xi intr t - xi intr 0) +
  sin (thetat intr 0) * (yi intr t - yi intr 0))%R.
intro; unfold xp in |- *; ring.
Qed.

Lemma ypt_yp0 :
 forall t : R,
 (yp t - yp 0)%R =
 (- sin (thetat intr 0) * (xi intr t - xi intr 0) +
  cos (thetat intr 0) * (yi intr t - yi intr 0))%R.
intro; unfold yp in |- *; ring.
Qed.

Lemma isometric_intruder :
 forall t : R,
 Rsqr_intruder_distance t = (Rsqr (xp t - xp 0) + Rsqr (yp t - yp 0))%R.
intro; unfold Rsqr_intruder_distance in |- *; rewrite xpt_xp0;
 rewrite ypt_yp0; repeat rewrite Rsqr_plus; ring_simplify;
 repeat rewrite Rsqr_mult;
 rewrite <- Rsqr_neg.
 pattern (Rsqr (xi intr t - xi intr 0)) at 1 in |- *.
 replace (Rsqr (xi intr t - xi intr 0)) with
 ((Rsqr (sin (thetat intr 0)) + Rsqr (cos (thetat intr 0))) *
  Rsqr (xi intr t - xi intr 0))%R.
 pattern (Rsqr (yi intr t - yi intr 0)) at 1 in |- *.
 replace (Rsqr (yi intr t - yi intr 0)) with
  ((Rsqr (sin (thetat intr 0)) + Rsqr (cos (thetat intr 0))) *
   Rsqr (yi intr t - yi intr 0))%R.
 ring.
 rewrite sin2_cos2 in |- *;  ring.
 rewrite sin2_cos2 in |- *;  ring.
Qed.

Lemma majoration :
 forall t : R,
 (Rsqr (yp t) <= Rsqr_evader_distance t)%R /\
 (Rsqr (xp t) <= Rsqr_evader_distance t)%R.
intro; generalize (isometric_evader t); intro; split;
 [ rewrite H; pattern (Rsqr (yp t)) at 1 in |- *;
    rewrite <- (Rplus_0_l (Rsqr (yp t))); apply Rplus_le_compat_r;
    apply Rle_0_sqr
 | rewrite H; pattern (Rsqr (xp t)) at 1 in |- *;
    rewrite <- (Rplus_0_r (Rsqr (xp t))); apply Rplus_le_compat_l;
    apply Rle_0_sqr ].
Qed.

Lemma YCNGFTYS_evader :
 forall t : R, (0 <= t)%R -> (l - v (vi intr) * t <= e t)%R.
intros; cut (i t <= vi intr * t)%R;
 [ intros; unfold Rminus in |- *; rewrite Rplus_comm;
    apply Rplus_le_reg_l with (vi intr * t)%R; repeat rewrite <- Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_l; rewrite Rplus_comm;
    apply Rle_trans with (e t + i t)%R;
    [ apply L_intruder | apply Rplus_le_compat_l; assumption ]
 | unfold i in |- *; unfold Rsqr_intruder_distance in |- *;
    apply (YCNGFTYS intr t H) ].
Qed.

Lemma YCNGSTYS_evader :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t < 2)%R -> (2 * r_vi * sin (rho_vi * (t / 2)) - l <= e t)%R.
intros; cut (2 * r_vi * sin (rho_vi * (t / 2)) <= i t)%R;
 [ intro; intros; unfold Rminus in |- *; rewrite Rplus_comm;
    apply Rplus_le_reg_l with l; repeat rewrite <- Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_l; apply Rle_trans with (i t);
    [ assumption | apply L_i ]
 | unfold i in |- *; unfold Rsqr_intruder_distance in |- *;
    apply (YCNGSTYS intr t H H0) ].
Qed.

Lemma xp_pos :
 forall t : R,
 (0 <= t)%R ->
 (rho_vi * t <= PI)%R -> Omega (beta + thetat intr 0) = true -> (0 <= xp t)%R.
intros; apply Rle_trans with (r_vi * sin (rho_vi * t))%R;
 [ apply Rmult_le_pos;
    [ unfold r_vi in |- *; unfold r in |- *; left; unfold Rdiv in |- *;
       apply Rmult_lt_0_compat;
       [ apply TypeSpeed_pos | apply Rinv_0_lt_compat; apply rho_pos ]
    | apply sin_ge_0;
       [ apply Rmult_le_pos;
          [ unfold rho_vi in |- *; left; apply rho_pos | assumption ]
       | assumption ] ]
 | apply (xpt_Omega t H H0 H1) ].
Qed.

Lemma no_conflict_xp_1_Omega :
 forall t : R,
 (1 <= t)%R ->
 (rho_vi * t <= PI - rho_vi)%R ->
 Omega (beta + thetat intr 0) = true -> (ConflictRange < xp t)%R.
Proof with trivial.
intros; apply Rlt_le_trans with (r_vi * sin rho_vi)%R...
apply r_sin_rho...
apply Rle_trans with (r_vi * sin (rho_vi * t))%R...
apply Rmult_le_compat_l...
left; unfold r_vi in |- *; unfold r in |- *; unfold Rdiv in |- *;
 apply Rmult_lt_0_compat...
apply TypeSpeed_pos...
apply Rinv_0_lt_compat; apply rho_pos...
case (Rle_dec (rho_vi * t) (PI / 2)); intro...
cut (rho_vi <= rho_vi * t)%R...
intro; apply sin_incr_1...
left; apply Rlt_trans with 0%R...
apply _PI2_RLT_0...
unfold rho_vi in |- *; apply rho_pos...
apply Rle_trans with (rho_vi * t)%R...
left; apply Rlt_le_trans with 0%R...
apply _PI2_RLT_0...
apply rho_t_pos...
left; apply Rlt_le_trans with 1%R; try apply Rlt_0_1...
pattern rho_vi at 1 in |- *; rewrite <- (Rmult_1_r rho_vi)...
apply Rmult_le_compat_l...
left; unfold rho_vi in |- *; apply rho_pos...
cut (PI / 2 < rho_vi * t)%R...
intro; cut (rho_vi <= PI - rho_vi * t)%R...
cut (PI - rho_vi * t <= PI / 2)%R...
intros; rewrite <- (sin_PI_x (rho_vi * t))...
apply sin_incr_1...
left; apply Rlt_trans with 0%R...
apply _PI2_RLT_0...
unfold rho_vi in |- *; apply rho_pos...
apply Rle_trans with (PI - rho_vi * t)%R...
apply Rle_trans with rho_vi...
left; apply Rlt_trans with 0%R...
apply _PI2_RLT_0...
unfold rho_vi in |- *; apply rho_pos...
left...
apply Rplus_lt_reg_l with (- (PI / 2) + rho_vi * t)%R...
replace (- (PI / 2) + rho_vi * t + (PI - rho_vi * t))%R with (PI / 2)%R...
replace (- (PI / 2) + rho_vi * t + PI / 2)%R with (rho_vi * t)%R...
ring...
unfold Rminus in |- *; unfold Rdiv in |- *;
 replace (- (PI * / 2) + rho_vi * t + (PI + - (rho_vi * t)))%R with
  (- (PI * / 2) + PI + (rho_vi * t + - (rho_vi * t)))%R...
rewrite Rplus_opp_r; rewrite Rplus_0_r...
pattern PI at 3 in |- *; rewrite double_var...
unfold Rdiv in |- *; ring...
ring...
apply Rplus_le_reg_l with (rho_vi * t - rho_vi)%R...
unfold Rminus in |- *...
repeat rewrite Rplus_assoc...
rewrite Rplus_opp_l; rewrite Rplus_0_r...
rewrite (Rplus_comm (rho_vi * t))...
repeat rewrite Rplus_assoc...
rewrite Rplus_opp_l; rewrite Rplus_0_r...
rewrite <- (Rplus_comm PI)...
auto with real...
cut (0 <= t)%R...
cut (rho_vi * t <= PI)%R...
intros...
generalize (xpt t H3 H2); intro...
generalize (xp0_pos H1); intro...
unfold Rminus in H4...
generalize (Rplus_le_compat_r (xp 0) (hx t) (xp t + - xp 0) H4)...
repeat rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r...
intro...
generalize (plus_le_is_le (hx t) (xp 0) (xp t) H5 H6)...
apply Rle_trans with (PI - rho_vi)%R...
apply Rplus_le_reg_l with (- PI)%R...
unfold Rminus in |- *...
repeat rewrite <- Rplus_assoc...
repeat rewrite Rplus_opp_l...
rewrite Rplus_0_l...
rewrite <- Ropp_0...
apply Ropp_ge_le_contravar; apply Rle_ge; left; unfold rho_vi in |- *;
 apply rho_pos...
left; apply Rlt_le_trans with 1%R; try apply Rlt_0_1...
Qed.

Lemma no_conflict_scenario_1_Omega :
 forall t : R,
 (1 <= t)%R ->
 (rho_vi * t <= PI - rho_vi)%R ->
 Omega (beta + thetat intr 0) = true ->
 (Rsqr ConflictRange < Rsqr_evader_distance t)%R.
Proof with trivial.
intros; apply Rlt_le_trans with (Rsqr (xp t))...
apply Rsqr_incrst_1...
apply (no_conflict_xp_1_Omega t H H0 H1)...
unfold ConflictRange in |- *; left; prove_sup...
cut ((0 <= t)%R /\ (rho_vi * t <= PI)%R)...
intro; elim H2; intros; apply (xp_pos t H3 H4 H1)...
split...
left; apply Rlt_le_trans with 1%R; try apply Rlt_0_1...
unfold Rminus in H0;
 generalize (Rplus_le_compat_r rho_vi (rho_vi * t) (PI + - rho_vi) H0);
 repeat rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r; 
 intro; apply (plus_le_is_le (rho_vi * t) rho_vi PI)...
unfold rho_vi in |- *; left; apply rho_pos...
elim (majoration t)...
Qed.

Lemma no_conflict_scenario_0_1s :
 forall t : R,
 (0 <= t)%R ->
 (t < 1)%R -> (ConflictRange + vi intr < l)%R -> (ConflictRange < e t)%R.
Proof with trivial.
intros; apply Rlt_le_trans with (l - vi intr * t)%R...
apply Rplus_lt_reg_l with (v (vi intr));
 rewrite <- (Rplus_comm ConflictRange); apply Rlt_trans with l...
apply Rplus_lt_reg_l with (- l)%R; rewrite Rplus_opp_l;
 replace (- l + (vi intr + (l - vi intr * t)))%R with (vi intr * (1 - t))%R...
apply Rmult_lt_0_compat...
apply TypeSpeed_pos...
generalize (Rplus_lt_compat_r (- t) t 1 H0); rewrite Rplus_opp_r...
unfold Rminus in |- *; rewrite Rmult_plus_distr_l; ring...
apply (YCNGFTYS_evader t H)...
Qed.

Lemma no_conflict_gt_max_t :
 forall t : R,
 let MaxDistance := (vi intr * t + ConflictRange)%R in
 (0 <= t)%R -> (MaxDistance < l)%R -> (ConflictRange < e t)%R.
Proof with trivial.
intros; apply Rlt_le_trans with (l - vi intr * t)%R...
unfold MaxDistance in H0; rewrite Rplus_comm in H0;
 generalize
  (Rplus_lt_compat_r (- (vi intr * t)) (ConflictRange + vi intr * t) l H0);
 repeat rewrite Rplus_assoc; rewrite Rplus_opp_r; rewrite Rplus_0_r...
apply (YCNGFTYS_evader t H)...
Qed.

Lemma no_conflict_lt_min_t :
 forall t : R,
 let MinDistance := (2 * r_vi * sin (rho_vi * (t / 2)) - ConflictRange)%R in
 (0 <= t)%R ->
 (0 <= rho_vi * t)%R ->
 (rho_vi * t < 2)%R -> (l < MinDistance)%R -> (ConflictRange < e t)%R.
Proof with trivial.
intros; apply Rlt_le_trans with (2 * r_vi * sin (rho_vi * (t / 2)) - l)%R...
unfold MinDistance in H2; apply Rplus_lt_reg_l with (- ConflictRange + l)%R;
 replace (- ConflictRange + l + ConflictRange)%R with l...
replace (- ConflictRange + l + (2 * r_vi * sin (rho_vi * (t / 2)) - l))%R
 with (2 * r_vi * sin (rho_vi * (t / 2)) - ConflictRange)%R; 
 try ring...
ring...
apply (YCNGSTYS_evader t H H1)...
Qed.

Lemma no_conflict_Omega_t :
 forall t : R,
 (ConflictRange + vi intr < l)%R ->
 (0 <= t)%R ->
 (rho_vi * t <= PI - rho_vi)%R ->
 Omega (beta + thetat intr 0) = true -> (ConflictRange < e t)%R.
intros; case (Rle_dec 1 t); intro.
apply Rsqr_incrst_0.
unfold e in |- *; rewrite Rsqr_sqrt. 
apply (no_conflict_scenario_1_Omega t r H1 H2).
apply Rsqr_evader_distance_pos.
left; unfold ConflictRange in |- *; prove_sup.
unfold e in |- *; apply sqrt_positivity; apply Rsqr_evader_distance_pos.
cut (t < 1)%R.
intro; apply (no_conflict_scenario_0_1s t H0 H3 H).
auto with real.
Qed.


(**********************************************************)
(************************** THEOREMS **********************)
(**********************************************************)


Theorem no_conflict_gt_max :
 let MaxDistance := (vi intr * T + ConflictRange)%R in
 (MaxDistance < l)%R -> conflict T = false.
Proof with trivial.
intros; unfold conflict in |- *; case (Rle_dec (Die T T) ConflictRange);
 intro...
cut (0 <= T)%R...
intro; generalize (no_conflict_gt_max_t T H0 H); intro; cut (e T = Die T T)...
intro; rewrite H2 in H1;
 elim
  (Rlt_irrefl (Die T T) (Rle_lt_trans (Die T T) ConflictRange (Die T T) r H1))...
left; apply Rlt_le_trans with MinT...
apply MinT_is_pos...
apply (cond_1 T)...
Qed.

Theorem no_conflict_lt_min :
 let MinDistance := (2 * r_vi * sin (rho_vi * (T / 2)) - ConflictRange)%R in
 (0 <= rho_vi * T)%R ->
 (rho_vi * T < 2)%R -> (l < MinDistance)%R -> conflict T = false.
Proof with trivial.
intros; unfold conflict in |- *; case (Rle_dec (Die T T) ConflictRange);
 intro...
cut (0 <= T)%R...
intro; generalize (no_conflict_lt_min_t T H2 H H0 H1); intro;
 cut (e T = Die T T)...
intro; rewrite H4 in H3;
 elim
  (Rlt_irrefl (Die T T) (Rle_lt_trans (Die T T) ConflictRange (Die T T) r H3))...
left; apply Rlt_le_trans with MinT; [ apply MinT_is_pos | apply (cond_1 T) ]...
Qed.

Theorem no_conflict_Omega :
 (ConflictRange + v (vi intr) < l)%R ->
 (rho_vi * T <= PI - rho_vi)%R ->
 Omega (beta + thetat intr 0) = true -> conflict T = false.
Proof with trivial.
intros; unfold conflict in |- *; case (Rle_dec (Die T T) ConflictRange);
 intro...
cut (0 <= T)%R...
intro; generalize (no_conflict_Omega_t T H H2 H0 H1); intro;
 cut (e T = Die T T)...
intro; rewrite H4 in H3;
 elim
  (Rlt_irrefl (Die T T) (Rle_lt_trans (Die T T) ConflictRange (Die T T) r H3))...
left; apply Rlt_le_trans with MinT; [ apply MinT_is_pos | apply (cond_1 T) ]...
Qed.

End trajectory.
