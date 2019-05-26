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


Section ycngstys.

Require Import Reals.
Require Import trajectory_def.
Require Import trajectory_const.
Require Import constants.
Require Import ycngftys.
Require Import rrho.

Unset Standard Proposition Elimination Names.

Variable intr : Trajectory.

Definition thetat : R -> R := theta intr.
Definition Rs (t : R) : R :=
  sqrt (Rsqr (xi intr t - xi intr 0) + Rsqr (yi intr t - yi intr 0)).

Axiom
  alphas_exists :
    { f : Differential_D2 |
       forall t : R,
       xi intr t = (Rs t * cos (f t) + xi intr 0)%R /\
       yi intr t = (Rs t * sin (f t) + yi intr 0)%R }.

Definition alphas := let (a,_) := alphas_exists in a.

Lemma alphas_def :
 forall t : R,
 xi intr t = (Rs t * cos (alphas t) + xi intr 0)%R /\
 yi intr t = (Rs t * sin (alphas t) + yi intr 0)%R.
unfold alphas in |- *; case alphas_exists; trivial.
Qed.

(**********)
Lemma Rsx : forall t : R, xi intr t = (xi intr 0 + Rs t * cos (alphas t))%R.
intros; generalize (alphas_def t); intro H; elim H; intros;
 rewrite Rplus_comm; assumption.
Qed.

Lemma Rsy : forall t : R, yi intr t = (yi intr 0 + Rs t * sin (alphas t))%R.
intros; generalize (alphas_def t); intro H; elim H; intros;
 rewrite Rplus_comm; assumption.
Qed.

Lemma Rs_x :
 forall t : R,
 cos (alphas t) <> 0%R -> Rs t = ((xi intr t - xi intr 0) / cos (alphas t))%R.
intros; rewrite Rsx; unfold Rminus, Rdiv in |- *;
 rewrite (Rplus_comm (xi intr 0)); rewrite Rplus_assoc; 
 rewrite Rplus_opp_r; rewrite Rplus_0_r; rewrite Rmult_assoc;
 rewrite <- Rinv_r_sym; [ rewrite Rmult_1_r; reflexivity | assumption ].
Qed.

Lemma Rs_y :
 forall t : R,
 sin (alphas t) <> 0%R -> Rs t = ((yi intr t - yi intr 0) / sin (alphas t))%R.
intros; rewrite Rsy; unfold Rminus, Rdiv in |- *;
 rewrite (Rplus_comm (yi intr 0)); rewrite Rplus_assoc; 
 rewrite Rplus_opp_r; rewrite Rplus_0_r; rewrite Rmult_assoc;
 rewrite <- Rinv_r_sym; [ rewrite Rmult_1_r; reflexivity | assumption ].
Qed.

(* With the two formulas above, you can prove the following result *)
(* Using the cos_sin_0's lemma                                     *)
Lemma Rs_derivable : derivable Rs.
unfold derivable in |- *; intro.
case (total_order_T (cos (alphas x)) 0); intro.
elim s; intro.
cut (cos (alphas x) <> 0%R).
intro;
 cut
  (exists eps : posreal,
     (forall h : R, (Rabs h < eps)%R -> cos (alphas (x + h)%R) <> 0%R)).
set (xi_p := fun t : R => xi intr t).
intro;
 cut (derivable_pt (fun t : R => ((xi_p t - xi_p 0) / cos (alphas t))%R) x).
intro X; unfold derivable_pt in X; elim X; intros l H1.
unfold derivable_pt in |- *; exists l.
unfold derivable_pt_abs in H1; unfold derivable_pt_lim in H1;
 unfold derivable_pt_abs in |- *; unfold derivable_pt_lim in |- *; 
 intros.
elim (H1 eps H2); intros del H3.
elim H0; intros dom H4.
cut (0 < Rmin del dom)%R.
intro; exists (mkposreal (Rmin del dom) H5); intros.
repeat rewrite Rs_x.
unfold xi_p in H3; apply H3.
assumption.
apply Rlt_le_trans with (Rmin del dom); [ apply H7 | apply Rmin_l ].
apply H.
apply H4; apply Rlt_le_trans with (Rmin del dom); [ apply H7 | apply Rmin_r ].
unfold Rmin in |- *; case (Rle_dec del dom); intro.
apply (cond_pos del).
apply (cond_pos dom).
set (alphas_p := d2 alphas); reg.
unfold alphas_p in |- *; apply (cond_D1 alphas).
apply (xi_derivable intr x).
set (alphas_p := d2 alphas); set (f := fun t : R => cos (alphas_p t)).
cut
 (exists eps : posreal,
    (forall h : R, (Rabs h < eps)%R -> f (x + h)%R <> 0%R)).
intro; elim H0; intros.
exists x0; intros; unfold f in H1; apply H1; assumption.
apply continuous_neq_0.
unfold f in |- *; reg; apply derivable_continuous_pt; apply (cond_D1 alphas).
apply H.
red in |- *; intro; rewrite H in a; elim (Rlt_irrefl _ a).
cut (sin (alphas x) <> 0%R).
intro;
 cut
  (exists eps : posreal,
     (forall h : R, (Rabs h < eps)%R -> sin (alphas (x + h)%R) <> 0%R)).
set (yi_p := fun t : R => yi intr t).
intro;
 cut (derivable_pt (fun t : R => ((yi_p t - yi_p 0) / sin (alphas t))%R) x).
intro X; unfold derivable_pt in X.
elim X; intros l H1.
unfold derivable_pt in |- *; exists l.
unfold derivable_pt_abs in H1; unfold derivable_pt_lim in H1;
 unfold derivable_pt_abs in |- *; unfold derivable_pt_lim in |- *; 
 intros.
elim (H1 eps H2); intros del H3.
elim H0; intros dom H4.
cut (0 < Rmin del dom)%R.
intro; exists (mkposreal (Rmin del dom) H5); intros.
repeat rewrite Rs_y.
unfold yi_p in H3; apply H3.
assumption.
apply Rlt_le_trans with (Rmin del dom); [ apply H7 | apply Rmin_l ].
apply H.
apply H4; apply Rlt_le_trans with (Rmin del dom); [ apply H7 | apply Rmin_r ].
unfold Rmin in |- *; case (Rle_dec del dom); intro.
apply (cond_pos del).
apply (cond_pos dom).
set (alphas_p := d2 alphas); reg.
unfold alphas_p in |- *; apply (cond_D1 alphas).
apply (yi_derivable intr x).
set (alphas_p := d2 alphas); set (f := fun t : R => sin (alphas_p t)).
cut
 (exists eps : posreal,
    (forall h : R, (Rabs h < eps)%R -> f (x + h)%R <> 0%R)).
intro; elim H0; intros.
exists x0; intros; unfold f in H1; apply H1; assumption.
apply continuous_neq_0.
unfold f in |- *; reg; apply derivable_continuous_pt; apply (cond_D1 alphas).
apply H.
assert (H := cos_sin_0_var (alphas x)); elim H; intro.
elim H0; assumption.
exact H0.
cut (cos (alphas x) <> 0%R).
intro;
 cut
  (exists eps : posreal,
     (forall h : R, (Rabs h < eps)%R -> cos (alphas (x + h)%R) <> 0%R)).
set (xi_p := fun t : R => xi intr t).
intro;
 cut (derivable_pt (fun t : R => ((xi_p t - xi_p 0) / cos (alphas t))%R) x).
intro X; unfold derivable_pt in X; elim X; intros l H1.
unfold derivable_pt in |- *; exists l.
unfold derivable_pt_abs in H1; unfold derivable_pt_lim in H1;
 unfold derivable_pt_abs in |- *; unfold derivable_pt_lim in |- *; 
 intros.
elim (H1 eps H2); intros del H3.
elim H0; intros dom H4.
cut (0 < Rmin del dom)%R.
intro; exists (mkposreal (Rmin del dom) H5); intros.
repeat rewrite Rs_x.
unfold xi_p in H3; apply H3.
assumption.
apply Rlt_le_trans with (Rmin del dom); [ apply H7 | apply Rmin_l ].
apply H.
apply H4; apply Rlt_le_trans with (Rmin del dom); [ apply H7 | apply Rmin_r ].
unfold Rmin in |- *; case (Rle_dec del dom); intro.
apply (cond_pos del).
apply (cond_pos dom).
set (alphas_p := d2 alphas); reg.
unfold alphas_p in |- *; apply (cond_D1 alphas).
apply (xi_derivable intr x).
set (alphas_p := d2 alphas); set (f := fun t : R => cos (alphas_p t)).
cut
 (exists eps : posreal,
    (forall h : R, (Rabs h < eps)%R -> f (x + h)%R <> 0%R)).
intro; elim H0; intros.
exists x0; intros; unfold f in H1; apply H1; assumption.
apply continuous_neq_0.
unfold f in |- *; reg; apply derivable_continuous_pt; apply (cond_D1 alphas).
apply H.
red in |- *; intro; rewrite H in r; elim (Rlt_irrefl _ r).
Qed.

Definition alphas_p : R -> R := d2 alphas.

Lemma fct_der4 :
 forall t : R,
 derivable_pt ((Rs * comp cos alphas_p)%F + fct_cte (xi intr 0)) t.
intro; reg. apply (cond_D1 alphas). 
apply Rs_derivable. 
Qed.

(**********)
Lemma Dxi :
 forall t : R,
 derive_pt (xi intr) t (xi_derivable intr t) =
 (derive_pt Rs t (Rs_derivable t) * cos (alphas t) -
  Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t))%R.
intro.
assert (H := fct_der4).
replace (derive_pt (xi intr) t (xi_derivable intr t)) with
 (derive_pt ((Rs * comp cos alphas_p)%F + fct_cte (xi intr 0)) t (H t)).
unfold plus_fct, mult_fct, comp, fct_cte in |- *.
set (H0 := Rs_derivable t).
cut (derivable_pt alphas_p t); [ intro X | apply (cond_D1 alphas) ].
replace (derive_pt alphas t (cond_D1 alphas t)) with (derive_pt alphas_p t X);
 [ idtac | apply pr_nu ].
reg.
unfold comp, alphas_p in |- *; ring.
unfold derive_pt in |- *.
case (H t).
case (xi_derivable intr t).
simpl.
intros.
eapply uniqueness_limite.
unfold derivable_pt_abs in d0.
apply d0.
unfold derivable_pt_lim in |- *; intros.
unfold derivable_pt_abs in d; unfold derivable_pt_lim in d.
elim (d eps H0); intros.
exists x1; intros.
unfold plus_fct, mult_fct, comp, fct_cte in |- *.
assert (H4 := H1 _ H2 H3).
replace
 ((Rs (t + h) * cos (alphas_p (t + h)) + xi intr 0 -
   (Rs t * cos (alphas_p t) + xi intr 0)) / h - x)%R with
 ((xi intr (t + h) - xi intr t) / h - x)%R.
apply H4.
rewrite (Rsx t).
rewrite (Rsx (t + h)).
replace
 (xi intr 0 + Rs (t + h) * cos (alphas (t + h)) -
  (xi intr 0 + Rs t * cos (alphas t)))%R with
 (Rs (t + h) * cos (alphas_p (t + h)) + xi intr 0 -
  (Rs t * cos (alphas_p t) + xi intr 0))%R.
reflexivity.
unfold alphas_p in |- *; ring.
Qed.

Lemma Dyi :
 forall t : R,
 derive_pt (yi intr) t (yi_derivable intr t) =
 (derive_pt Rs t (Rs_derivable t) * sin (alphas t) +
  Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t))%R.
intro.
set (H := Rs_derivable t).
cut (derivable_pt alphas_p t); [ intro X | apply (cond_D1 alphas) ].
cut (derivable_pt ((Rs * comp sin alphas_p)%F + fct_cte (yi intr 0)) t);
 [ intro X0 | reg ].
replace (derive_pt (yi intr) t (yi_derivable intr t)) with
 (derive_pt ((Rs * comp sin alphas_p)%F + fct_cte (yi intr 0)) t X0).
replace (derive_pt alphas t (cond_D1 alphas t)) with (derive_pt alphas_p t X);
 [ idtac | apply pr_nu ].
unfold plus_fct, mult_fct, comp, fct_cte in |- *.
reg.
unfold comp, alphas_p in |- *; ring.
unfold derive_pt in |- *.
case X0.
case (yi_derivable intr t).
simpl.
intros.
eapply uniqueness_limite.
unfold derivable_pt_abs in d0.
apply d0.
unfold derivable_pt_lim in |- *; intros.
unfold derivable_pt_abs in d; unfold derivable_pt_lim in d.
elim (d eps H0); intros.
exists x1; intros.
unfold plus_fct, mult_fct, comp, fct_cte in |- *.
assert (H4 := H1 _ H2 H3).
replace
 ((Rs (t + h) * sin (alphas_p (t + h)) + yi intr 0 -
   (Rs t * sin (alphas_p t) + yi intr 0)) / h - x)%R with
 ((yi intr (t + h) - yi intr t) / h - x)%R.
apply H4.
rewrite (Rsy t).
rewrite (Rsy (t + h)).
replace
 (yi intr 0 + Rs (t + h) * sin (alphas (t + h)) -
  (yi intr 0 + Rs t * sin (alphas t)))%R with
 (Rs (t + h) * sin (alphas_p (t + h)) + yi intr 0 -
  (Rs t * sin (alphas_p t) + yi intr 0))%R.
reflexivity.
unfold alphas_p in |- *; ring.
Qed.

(**********)
Lemma DRs_cos :
 forall t : R,
 (derive_pt Rs t (Rs_derivable t) * cos (alphas t) -
  Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t))%R =
 (vi intr * cos (thetat t))%R.
intro.
assert (H := Dxi t).
unfold xi in H.
assert (H0 := cond_x intr t).
cut
 (derive_pt (x intr) t (xi_derivable intr t) =
  derive_pt (x intr) t (cond_diff (x intr) t)); [ intro | apply pr_nu ].
rewrite H1 in H.
rewrite H0 in H.
unfold vi, thetat in |- *; symmetry  in |- *; assumption.
Qed.

Lemma DRs_sin :
 forall t : R,
 (derive_pt Rs t (Rs_derivable t) * sin (alphas t) +
  Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t))%R =
 (vi intr * sin (thetat t))%R.
intro; assert (H := Dyi t).
unfold yi in H; assert (H0 := cond_y intr t).
cut
 (derive_pt (y intr) t (yi_derivable intr t) =
  derive_pt (y intr) t (cond_diff (y intr) t)); [ intro | apply pr_nu ].
rewrite H1 in H.
rewrite H0 in H.
unfold vi, thetat in |- *; symmetry  in |- *; assumption.
Qed.

(**********)
Lemma eq_plus_eq_is_eq :
 forall x y z t : R, x = y -> z = t -> (x + z)%R = (y + t)%R.
intros; rewrite H; rewrite H0; reflexivity.
Qed.

(**********)
Lemma DRs :
 forall t : R,
 derive_pt Rs t (Rs_derivable t) = (vi intr * cos (thetat t - alphas t))%R.
intro.
assert (H := DRs_cos t).
assert (H0 := DRs_sin t).
assert (H1 := Rmult_eq_compat_l (cos (alphas t)) _ _ H).
assert (H2 := Rmult_eq_compat_l (sin (alphas t)) _ _ H0).
replace (derive_pt Rs t (Rs_derivable t)) with
 (cos (alphas t) *
  (derive_pt Rs t (Rs_derivable t) * cos (alphas t) -
   Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t)) +
  sin (alphas t) *
  (derive_pt Rs t (Rs_derivable t) * sin (alphas t) +
   Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t)))%R.
replace (vi intr * cos (thetat t - alphas t))%R with
 (cos (alphas t) * (vi intr * cos (thetat t)) +
  sin (alphas t) * (vi intr * sin (thetat t)))%R.
apply eq_plus_eq_is_eq; assumption.
rewrite cos_minus; ring.
unfold Rminus in |- *.
repeat rewrite Rmult_plus_distr_l.
replace
 (cos (alphas t) * (derive_pt Rs t (Rs_derivable t) * cos (alphas t)) +
  cos (alphas t) *
  - (Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t)) +
  (sin (alphas t) * (derive_pt Rs t (Rs_derivable t) * sin (alphas t)) +
   sin (alphas t) *
   (Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t))))%R with
 (derive_pt Rs t (Rs_derivable t) *
  (Rsqr (sin (alphas t)) + Rsqr (cos (alphas t))) +
  cos (alphas t) *
  - (Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t)) +
  sin (alphas t) *
  (Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t)))%R;
 [ idtac | unfold Rsqr in |- *; ring ].
rewrite sin2_cos2; ring.
Qed.

(**********)
Lemma Rs_alphas :
 forall t : R,
 (Rs t * derive_pt alphas t (cond_D1 alphas t))%R =
 (vi intr * sin (thetat t - alphas t))%R.
intro.
assert (H := DRs_cos t).
assert (H0 := DRs_sin t). 
assert (H1 := Rmult_eq_compat_l (- sin (alphas t)) _ _ H).
assert (H2 := Rmult_eq_compat_l (cos (alphas t)) _ _ H0).
replace (Rs t * derive_pt alphas t (cond_D1 alphas t))%R with
 (- sin (alphas t) *
  (derive_pt Rs t (Rs_derivable t) * cos (alphas t) -
   Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t)) +
  cos (alphas t) *
  (derive_pt Rs t (Rs_derivable t) * sin (alphas t) +
   Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t)))%R.
replace (vi intr * sin (thetat t - alphas t))%R with
 (- sin (alphas t) * (vi intr * cos (thetat t)) +
  cos (alphas t) * (vi intr * sin (thetat t)))%R.
apply eq_plus_eq_is_eq; assumption.
rewrite sin_minus; ring.
unfold Rminus in |- *.
repeat rewrite Rmult_plus_distr_l.
replace
 (- sin (alphas t) * (derive_pt Rs t (Rs_derivable t) * cos (alphas t)) +
  - sin (alphas t) *
  - (Rs t * sin (alphas t) * derive_pt alphas t (cond_D1 alphas t)) +
  (cos (alphas t) * (derive_pt Rs t (Rs_derivable t) * sin (alphas t)) +
   cos (alphas t) *
   (Rs t * cos (alphas t) * derive_pt alphas t (cond_D1 alphas t))))%R with
 (Rs t * derive_pt alphas t (cond_D1 alphas t) *
  (Rsqr (sin (alphas t)) + Rsqr (cos (alphas t))) +
  cos (alphas t) * - sin (alphas t) * derive_pt Rs t (Rs_derivable t) +
  sin (alphas t) * cos (alphas t) * derive_pt Rs t (Rs_derivable t))%R;
 [ idtac | unfold Rsqr in |- *; ring ].
rewrite sin2_cos2; ring.
Qed.

Lemma fct_der5 :
 forall t : R,
 derivable_pt (fun y : R => (Rs y * derive_pt alphas y (cond_D1 alphas y))%R)
   t.
intro; set (alpha_p := d2 alphas);
 set (f := fun x : R => derive_pt alpha_p x (cond_D1 alphas x)).
change (derivable_pt (fun y : R => (Rs y * f y)%R) t) in |- *.
reg.
apply (cond_D2 alphas).
apply Rs_derivable.
Qed.

(**********)
Lemma D_Rs_alphas1 :
 forall t : R,
 derive_pt (fun y : R => (Rs y * derive_pt alphas y (cond_D1 alphas y))%R) t
   (fct_der5 t) =
 (derive_pt Rs t (Rs_derivable t) * derive_pt alphas t (cond_D1 alphas t) +
  Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t))%R.
intro.
set (f := fun x : R => derive_pt alphas x (cond_D1 alphas x)).
replace
 (derive_pt (fun y : R => (Rs y * derive_pt alphas y (cond_D1 alphas y))%R) t
    (fct_der5 t)) with
 (derive_pt (fun y : R => (Rs y * f y)%R) t (fct_der5 t));
 [ idtac | reflexivity ].
replace (derive_pt alphas t (cond_D1 alphas t)) with (f t);
 [ idtac | reflexivity ].
replace (derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t))
 with (derive_pt f t (cond_D2 alphas t)); [ idtac | reflexivity ].
cut (derivable_pt Rs t); [ intro X | apply Rs_derivable ].
cut (derivable_pt f t); [ intro X0 | apply (cond_D2 alphas) ].
reg.
replace (derive_pt f t (cond_D2 alphas t)) with (derive_pt f t X0);
 [ idtac | apply pr_nu ].
replace (derive_pt Rs t (Rs_derivable t)) with (derive_pt Rs t X);
 [ idtac | apply pr_nu ].
ring.
Qed.

(**********)
Lemma thetat_derivable : derivable thetat.
unfold thetat in |- *; apply (cond_diff (theta intr)).
Qed.

(**********)
Lemma D_Rs_alphas2 :
 forall t : R,
 derive_pt (fun y : R => (Rs y * derive_pt alphas y (cond_D1 alphas y))%R) t
   (fct_der5 t) =
 (vi intr * cos (thetat t - alphas t) *
  (derive_pt thetat t (thetat_derivable t) -
   derive_pt alphas t (cond_D1 alphas t)))%R.
intro.
cut (derivable_pt (fun x : R => (vi intr * sin (thetat x - alphas x))%R) t).
intro X.
replace
 (derive_pt (fun y : R => (Rs y * derive_pt alphas y (cond_D1 alphas y))%R) t
    (fct_der5 t)) with
 (derive_pt (fun x : R => (vi intr * sin (thetat x - alphas x))%R) t X).
set (f := d2 alphas).
cut (derivable_pt f t); [ intro X0 | apply (cond_D1 alphas) ].
cut (derivable_pt thetat t); [ intro X1 | apply thetat_derivable ].
reg.
unfold fct_cte, minus_fct in |- *.
replace (derive_pt f t (cond_D1 alphas t)) with (derive_pt f t X0);
 [ idtac | apply pr_nu ].
replace (derive_pt thetat t (thetat_derivable t)) with
 (derive_pt thetat t X1); [ idtac | apply pr_nu ].
ring.
unfold derive_pt in |- *.
case X; case (fct_der5 t); simpl; intros.
eapply uniqueness_limite.
unfold derivable_pt_abs in d0; apply d0.
unfold derivable_pt_lim in |- *; intros.
unfold derivable_pt_abs in d; unfold derivable_pt_lim in d; elim (d eps H);
 intros.
exists x1; intros.
do 2 rewrite <- Rs_alphas.
apply H0; assumption.
fold alphas_p in |- *; reg.
apply (cond_D1 alphas).
apply thetat_derivable.
Qed.

(**********)
Lemma D_Rs_2 :
 forall t : R,
 (derive_pt Rs t (Rs_derivable t) *
  (2 * derive_pt alphas t (cond_D1 alphas t) -
   derive_pt thetat t (thetat_derivable t)))%R =
 (- Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t))%R.
intro.
assert (H := D_Rs_alphas1 t).
assert (H0 := D_Rs_alphas2 t).
assert (H1 := DRs t).
rewrite H in H0; rewrite <- H1 in H0.
assert
 (H2 :=
  Rplus_eq_compat_l
    (- derive_pt Rs t (Rs_derivable t) *
     (derive_pt thetat t (thetat_derivable t) -
      derive_pt alphas t (cond_D1 alphas t)) +
     - Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t))
    _ _ H0).
cut
 ((- derive_pt Rs t (Rs_derivable t) *
   (derive_pt thetat t (thetat_derivable t) -
    derive_pt alphas t (cond_D1 alphas t)) +
   - Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t) +
   (derive_pt Rs t (Rs_derivable t) * derive_pt alphas t (cond_D1 alphas t) +
    Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t)))%R =
  (derive_pt Rs t (Rs_derivable t) *
   (2 * derive_pt alphas t (cond_D1 alphas t) -
    derive_pt thetat t (thetat_derivable t)))%R); [ intro | ring ].
cut
 ((- derive_pt Rs t (Rs_derivable t) *
   (derive_pt thetat t (thetat_derivable t) -
    derive_pt alphas t (cond_D1 alphas t)) +
   - Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t) +
   derive_pt Rs t (Rs_derivable t) *
   (derive_pt thetat t (thetat_derivable t) -
    derive_pt alphas t (cond_D1 alphas t)))%R =
  (- Rs t * derive_pt (derive alphas (cond_D1 alphas)) t (cond_D2 alphas t))%R);
 [ intro | ring ].
rewrite H3 in H2; rewrite H4 in H2.
assumption.
Qed.

(**********)
Lemma Rsqr_DRs :
 forall t : R,
 (Rsqr (derive_pt Rs t (Rs_derivable t)) +
  Rsqr (Rs t) * Rsqr (derive_pt alphas t (cond_D1 alphas t)))%R =
 Rsqr (vi intr).
intro; rewrite <- Rsqr_mult; rewrite DRs; rewrite Rs_alphas;
 repeat rewrite Rsqr_mult; rewrite Rplus_comm;
 rewrite <- (Rmult_comm (Rsqr (cos (thetat t - alphas t))));
 rewrite <- (Rmult_comm (Rsqr (sin (thetat t - alphas t))));
 rewrite <- Rmult_plus_distr_r; rewrite sin2_cos2; 
 rewrite Rmult_1_l; reflexivity.
Qed.

(**********)
Lemma Rs_pos : forall t : R, (0 <= Rs t)%R.
intro; unfold Rs in |- *; apply sqrt_positivity; apply Rplus_le_le_0_compat;
 apply Rle_0_sqr.
Qed.

Lemma Rs_0 : Rs 0 = 0%R.
unfold Rs in |- *; unfold Rminus in |- *; repeat rewrite Rplus_opp_r;
 repeat rewrite Rsqr_0; rewrite Rplus_0_r; rewrite sqrt_0; 
 reflexivity.
Qed.

(**********)
Lemma D_Rs_0 : (0 <= derive_pt Rs 0 (Rs_derivable 0))%R.
case (Rtotal_order 0 (derive_pt Rs 0 (Rs_derivable 0%R))); intro.
left; assumption.
elim H; intro.
right; assumption.
generalize (derivable_derive Rs 0 (Rs_derivable 0%R)); intro; elim H1;
 intros l H2; rewrite H2 in H0.
generalize (derive_pt_eq_1 Rs 0 l (Rs_derivable 0%R) H2); intros;
 cut (0 < - (l / 2))%R.
intro H4; elim (H3 (- (l / 2))%R H4).
intros; cut ((x / 2)%R <> 0%R).
intro H6; cut (Rabs (x / 2) < x)%R.
intro H7; generalize (H5 (x / 2)%R H6 H7); intro H8; rewrite Rs_0 in H8;
 rewrite Rplus_0_l in H8; unfold Rminus in H8; rewrite Ropp_0 in H8;
 rewrite Rplus_0_r in H8;
 generalize (Rabs_def2 (Rs (x / 2) / (x / 2) + - l) (- (l / 2)) H8); 
 intro H9; elim H9; intros;
 generalize
  (Rplus_lt_compat_r l (Rs (x / 2) / (x / 2) + - l) (- (l / 2)) H10);
 rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
 replace (- (l / 2) + l)%R with (l / 2)%R.
intro H12; cut (l / 2 < 0)%R.
intro H13; generalize (Rlt_trans (Rs (x / 2) / (x / 2)) (l / 2) 0 H12 H13);
 intro H14; unfold Rdiv in H14; cut (0 < x * / 2)%R.
intro H15;
 generalize
  (Rmult_lt_compat_r (x * / 2) (Rs (x * / 2) * / (x * / 2)) 0 H15 H14);
 rewrite Rmult_0_l; rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
rewrite Rmult_1_r; intro H16;
 elim (Rlt_irrefl 0 (Rle_lt_trans 0 (Rs (x * / 2)) 0 (Rs_pos (x * / 2)) H16)).
apply prod_neq_R0.
generalize (cond_pos x); intro H16; red in |- *; intro H17;
 rewrite H17 in H16; elim (Rlt_irrefl 0 H16).
apply Rinv_neq_0_compat; discrR.
apply Rmult_lt_0_compat;
 [ apply (cond_pos x) | apply Rinv_0_lt_compat; prove_sup0 ].
assert (Hyp : (0 < 2)%R).
prove_sup0.
unfold Rdiv in |- *;
 generalize (Rmult_lt_compat_r (/ 2) l 0 (Rinv_0_lt_compat 2 Hyp) H0);
 rewrite Rmult_0_l; intro H13; exact H13.
pattern l at 3 in |- *; rewrite double_var.
ring.
cut (0 < x / 2)%R.
intro H7; apply Rabs_def1.
pattern x at 1 in |- *; replace (pos x) with (2 * (x / 2))%R.
pattern (x / 2)%R at 1 in |- *; replace (x / 2)%R with (x / 2 + 0)%R.
replace (2 * (x / 2))%R with (x / 2 + x / 2)%R.
apply Rplus_lt_compat_l; assumption.
ring.
apply Rplus_0_r.
pattern (pos x) at 2 in |- *; rewrite double_var.
ring.
apply Rlt_trans with 0%R.
rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; apply (cond_pos x).
assumption.
unfold Rdiv in |- *; apply Rmult_lt_0_compat;
 [ apply (cond_pos x) | apply Rinv_0_lt_compat; prove_sup0 ].
unfold Rdiv in |- *; apply prod_neq_R0.
generalize (cond_pos x); intro H6; red in |- *; intro H7; rewrite H7 in H6;
 elim (Rlt_irrefl 0 H6).
apply Rinv_neq_0_compat; discrR.
assert (Hyp : (0 < 2)%R).
prove_sup0.
unfold Rdiv in |- *; rewrite <- Ropp_0; apply Ropp_lt_gt_contravar;
 generalize (Rmult_lt_compat_r (/ 2) l 0 (Rinv_0_lt_compat 2 Hyp) H0);
 rewrite Rmult_0_l; intro H4; assumption.
Qed.

Lemma eq_sym : forall x y : R, x = y -> y = x.
intros; rewrite H; reflexivity.
Qed.

(**********)
Lemma D_Rs_0_strong : (0 < derive_pt Rs 0 (Rs_derivable 0))%R.
case (Rtotal_order 0 (derive_pt Rs 0 (Rs_derivable 0%R))); intro.
assumption.
elim H; intro.
generalize (Rsqr_DRs 0); intro H1; rewrite <- H0 in H1; rewrite Rs_0 in H1;
 repeat rewrite Rsqr_0 in H1; rewrite Rplus_0_l in H1;
 rewrite Rmult_0_l in H1; generalize (eq_sym 0 (Rsqr (vi intr)) H1).
clear H1; intro H1; generalize (Rsqr_eq_0 (vi intr) H1).
intro H2; generalize (TypeSpeed_pos (vi intr)); intro H3; rewrite H2 in H3;
 elim (Rlt_irrefl 0 H3).
generalize D_Rs_0; intro H1;
 elim
  (Rlt_irrefl 0 (Rle_lt_trans 0 (derive_pt Rs 0 (Rs_derivable 0%R)) 0 H1 H0)).
Qed.

(**********)
Lemma D_alphas_0 :
 (2 * derive_pt alphas 0 (cond_D1 alphas 0))%R =
 derive_pt thetat 0 (thetat_derivable 0%R).
generalize (D_Rs_2 0); intro; rewrite Rs_0 in H; rewrite Ropp_0 in H;
 rewrite Rmult_0_l in H;
 generalize
  (Rmult_integral (derive_pt Rs 0 (Rs_derivable 0%R))
     (2 * derive_pt alphas 0 (cond_D1 alphas 0%R) -
      derive_pt thetat 0 (thetat_derivable 0%R)) H); 
 intro H1; elim H1; intro; generalize D_Rs_0_strong; 
 intro.
rewrite H0 in H2; elim (Rlt_irrefl 0 H2).
generalize
 (Rminus_diag_uniq_sym (derive_pt thetat 0 (thetat_derivable 0%R))
    (2 * derive_pt alphas 0 (cond_D1 alphas 0%R)) H0); 
 intro; symmetry  in |- *; assumption.
Qed.

(**********)
Lemma D_Rs_pos_non_null :
 forall t : R,
 (0 < t)%R ->
 (forall x : R, (0 < x < t)%R -> (0 < derive_pt Rs x (Rs_derivable x))%R) ->
 (0 < Rs t)%R.
intros; generalize (derive_increasing_interv 0 t Rs Rs_derivable H H0);
 intros; cut (0 <= 0 <= t)%R;
 [ cut (0 <= t <= t)%R;
    [ intros; rewrite <- Rs_0; apply (H1 0%R t H3 H2 H)
    | split; [ left; assumption | right; reflexivity ] ]
 | split; [ right; reflexivity | left; assumption ] ].
Qed.

(* To prove the following axioms, you need more sophisticated analysis *)
Axiom
  D_Rs_pos :
    forall t : R,
    (0 <= t)%R ->
    (t < 2 / rho (vi intr))%R -> (0 < derive_pt Rs t (Rs_derivable t))%R.

Axiom
  D_abs_alpha :
    forall t : R,
    (0 <= t)%R ->
    (t < 2 / rho (vi intr))%R ->
    (- rho (vi intr) / 2 <= derive_pt alphas t (cond_D1 alphas t))%R /\
    (derive_pt alphas t (cond_D1 alphas t) <= rho (vi intr) / 2)%R.

Definition F (t : R) : R :=
  (2 * (vi intr / rho (vi intr)) * sin (rho (vi intr) * (t / 2)))%R.

Lemma F_derivable : derivable F.
unfold F in |- *; reg.
Qed.

(**********)
Lemma D_F :
 forall t : R,
 derive_pt F t (F_derivable t) = (vi intr * cos (rho (vi intr) * (t / 2)))%R.
intro; unfold F in |- *; reg.
unfold Rdiv in |- *;  field.
assert (H0 := rho_pos (vi intr)); red in |- *; intro; rewrite H in H0;
 elim (Rlt_irrefl 0 H0).
Qed.

(**********)
Lemma D_F_Rsqr_v :
 forall t : R,
 (Rsqr (derive_pt F t (F_derivable t)) +
  Rsqr (rho (vi intr) / 2) * Rsqr (F t))%R = Rsqr (vi intr).
intro; rewrite (D_F t); rewrite <- Rsqr_mult;
 cut
  ((rho (vi intr) / 2 * F t)%R = (vi intr * sin (rho (vi intr) * (t / 2)))%R).
intro H; rewrite H; repeat rewrite Rsqr_mult;
 replace
  (Rsqr (vi intr) * Rsqr (cos (rho (vi intr) * (t / 2))) +
   Rsqr (vi intr) * Rsqr (sin (rho (vi intr) * (t / 2))))%R with
  (Rsqr (vi intr) *
   (Rsqr (sin (rho (vi intr) * (t / 2))) +
    Rsqr (cos (rho (vi intr) * (t / 2)))))%R.
rewrite sin2_cos2; rewrite Rmult_1_r; reflexivity.
ring.
unfold F in |- *; unfold Rdiv in |- *; rewrite <- Rmult_assoc;
 replace (rho (vi intr) * / 2 * (2 * (vi intr * / rho (vi intr))))%R with
  (2 * / 2 * (rho (vi intr) * / rho (vi intr)) * vi intr)%R.
repeat rewrite <- Rinv_r_sym.
repeat rewrite Rmult_1_l; reflexivity.
generalize (rho_pos (vi intr)); intro; red in |- *; intro; rewrite H0 in H;
 elim (Rlt_irrefl 0 H).
discrR.
ring.
Qed.

Definition G (t : R) : R := (Rs t - F t)%R.

Lemma G_derivable : derivable G.
unfold G in |- *; reg.
apply F_derivable.
apply Rs_derivable.
Qed.

(**********)
Lemma D_G_alphas :
 forall t : R,
 (derive_pt G t (G_derivable t) *
  (derive_pt Rs t (Rs_derivable t) + derive_pt F t (F_derivable t)))%R =
 (- Rsqr (derive_pt alphas t (cond_D1 alphas t)) * G t * (Rs t + F t) +
  Rsqr (F t) *
  (Rsqr (rho (vi intr) / 2) - Rsqr (derive_pt alphas t (cond_D1 alphas t))))%R.
intro.
cut
 (derive_pt G t (G_derivable t) =
  (derive_pt Rs t (Rs_derivable t) - derive_pt F t (F_derivable t))%R).
intro; rewrite H;
 rewrite
  (Rsqr_minus_plus (derive_pt Rs t (Rs_derivable t))
     (derive_pt F t (F_derivable t))); unfold G in |- *;
 repeat rewrite Rmult_assoc; rewrite (Rsqr_minus_plus (Rs t) (F t)).
replace
 (- Rsqr (derive_pt alphas t (cond_D1 alphas t)) * (Rsqr (Rs t) - Rsqr (F t)) +
  Rsqr (F t) *
  (Rsqr (rho (vi intr) / 2) - Rsqr (derive_pt alphas t (cond_D1 alphas t))))%R
 with
 (- Rsqr (derive_pt alphas t (cond_D1 alphas t)) * Rsqr (Rs t) +
  Rsqr (F t) * Rsqr (rho (vi intr) / 2))%R.
apply
 Rplus_eq_reg_l
  with
    (Rsqr (derive_pt F t (F_derivable t)) +
     Rsqr (derive_pt alphas t (cond_D1 alphas t)) * Rsqr (Rs t))%R.
replace
 (Rsqr (derive_pt F t (F_derivable t)) +
  Rsqr (derive_pt alphas t (cond_D1 alphas t)) * Rsqr (Rs t) +
  (Rsqr (derive_pt Rs t (Rs_derivable t)) -
   Rsqr (derive_pt F t (F_derivable t))))%R with
 (Rsqr (derive_pt Rs t (Rs_derivable t)) +
  Rsqr (Rs t) * Rsqr (derive_pt alphas t (cond_D1 alphas t)))%R.
replace
 (Rsqr (derive_pt F t (F_derivable t)) +
  Rsqr (derive_pt alphas t (cond_D1 alphas t)) * Rsqr (Rs t) +
  (- Rsqr (derive_pt alphas t (cond_D1 alphas t)) * Rsqr (Rs t) +
   Rsqr (F t) * Rsqr (rho (vi intr) / 2)))%R with
 (Rsqr (derive_pt F t (F_derivable t)) +
  Rsqr (rho (vi intr) / 2) * Rsqr (F t))%R.
rewrite Rsqr_DRs; rewrite D_F_Rsqr_v; reflexivity.
ring.
ring.
ring.
unfold G in |- *.
cut (derivable_pt Rs t); [ intro X | apply Rs_derivable ].
cut (derivable_pt F t); [ intro X0 | apply F_derivable ].
reg.
replace (derive_pt F t (F_derivable t)) with (derive_pt F t X0);
 [ idtac | apply pr_nu ].
replace (derive_pt Rs t (Rs_derivable t)) with (derive_pt Rs t X);
 [ idtac | apply pr_nu ].
ring.
Qed.

(**********)
Lemma Rlt_1_PI2 : (1 < PI / 2)%R.
generalize PI_approx; intro; elim H; intros.
apply Rlt_le_trans with (PI_lb / 2)%R.
unfold PI_lb in |- *; unfold Rdiv in |- *; apply Rmult_lt_reg_l with 2%R.
prove_sup.
rewrite Rmult_1_r; rewrite <- Rmult_assoc; rewrite Rinv_r_simpl_m;
 [ prove_sup | discrR ].
left; unfold Rdiv in |- *; repeat rewrite <- (Rmult_comm (/ 2));
 apply Rmult_lt_compat_l; [ apply Rinv_0_lt_compat; prove_sup | assumption ].
Qed.

(**********)
Lemma D_G_pos :
 forall t : R,
 (0 <= t)%R ->
 (t < 2 / rho (vi intr))%R ->
 (G t <= 0)%R -> (0 <= derive_pt G t (G_derivable t))%R.
intros.
case (Rcase_abs (derive_pt G t (G_derivable t))); intro.
generalize (D_G_alphas t); intro.
generalize (D_Rs_pos t H H0); intro.
cut (0 <= derive_pt F t (F_derivable t))%R.
intro.
generalize (Rs_pos t); intro.
cut (0 <= F t)%R.
intro.
cut
 (derive_pt G t (G_derivable t) *
  (derive_pt Rs t (Rs_derivable t) + derive_pt F t (F_derivable t)) < 0)%R.
intro.
cut
 (0 <=
  - Rsqr (derive_pt alphas t (cond_D1 alphas t)) * G t * (Rs t + F t) +
  Rsqr (F t) *
  (Rsqr (rho (vi intr) / 2) - Rsqr (derive_pt alphas t (cond_D1 alphas t))))%R.
intro.
rewrite <- H2 in H8.
elim
 (Rlt_irrefl 0
    (Rle_lt_trans 0
       (derive_pt G t (G_derivable t) *
        (derive_pt Rs t (Rs_derivable t) + derive_pt F t (F_derivable t))) 0
       H8 H7)).
apply Rplus_le_le_0_compat.
replace
 (- Rsqr (derive_pt alphas t (cond_D1 alphas t)) * G t * (Rs t + F t))%R with
 (Rsqr (derive_pt alphas t (cond_D1 alphas t)) * - G t * (Rs t + F t))%R.
repeat simple apply Rmult_le_pos.
apply Rle_0_sqr.
rewrite <- Ropp_0.
apply Ropp_ge_le_contravar.
apply Rle_ge; assumption.
apply Rplus_le_le_0_compat; assumption.
ring.
apply Rmult_le_pos.
apply Rle_0_sqr.
apply Rplus_le_reg_l with (Rsqr (derive_pt alphas t (cond_D1 alphas t))).
rewrite Rplus_0_r.
rewrite Rplus_comm.
unfold Rminus in |- *.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
generalize (D_abs_alpha t H H0); intro.
elim H8; intros.
case (Rtotal_order 0 (derive_pt alphas t (cond_D1 alphas t))); intro.
apply Rsqr_incr_1.
assumption.
left; assumption.
unfold Rdiv in |- *; left; apply Rmult_lt_0_compat.
apply rho_pos.
apply Rinv_0_lt_compat; prove_sup0.
elim H11; intros.
rewrite <- H12.
rewrite Rsqr_0.
apply Rle_0_sqr.
rewrite (Rsqr_neg (derive_pt alphas t (cond_D1 alphas t))).
apply Rsqr_incr_1. 
rewrite <- (Ropp_involutive (rho (vi intr) / 2)).
apply Ropp_ge_le_contravar.
apply Rle_ge.
replace (- (rho (vi intr) / 2))%R with (- rho (vi intr) / 2)%R.
assumption.
unfold Rdiv in |- *; ring.
rewrite <- Ropp_0.
apply Ropp_ge_le_contravar; apply Rle_ge; left; assumption.
unfold Rdiv in |- *; left; apply Rmult_lt_0_compat.
apply rho_pos.
apply Rinv_0_lt_compat; prove_sup0.
rewrite <- (Ropp_involutive 0).
replace
 (derive_pt G t (G_derivable t) *
  (derive_pt Rs t (Rs_derivable t) + derive_pt F t (F_derivable t)))%R with
 (-
  (- derive_pt G t (G_derivable t) *
   (derive_pt Rs t (Rs_derivable t) + derive_pt F t (F_derivable t))))%R.
apply Ropp_lt_gt_contravar.
rewrite Ropp_0.
apply Rmult_lt_0_compat.
rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; assumption.
apply Rplus_lt_le_0_compat; assumption.
ring.
unfold F in |- *.
repeat simple apply Rmult_le_pos.
left; prove_sup0.
unfold Rdiv in |- *; left; apply Rmult_lt_0_compat.
apply TypeSpeed_pos.
apply Rinv_0_lt_compat; apply rho_pos.
apply sin_ge_0.
unfold Rdiv in |- *; repeat simple apply Rmult_le_pos.
left; apply rho_pos.
assumption.
left; apply Rinv_0_lt_compat; prove_sup0.
left; apply Rlt_trans with 1%R.
unfold Rdiv in |- *.
apply Rmult_lt_reg_l with (2 * / rho (vi intr))%R.
apply Rmult_lt_0_compat;
 [ prove_sup0 | apply Rinv_0_lt_compat; apply rho_pos ].
rewrite Rmult_1_r.
replace (2 * / rho (vi intr) * (rho (vi intr) * (t * / 2)))%R with t.
assumption.
repeat rewrite Rmult_assoc.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
rewrite <- Rinv_l_sym.
repeat rewrite <- Rmult_assoc.
rewrite <- Rinv_l_sym.
rewrite Rmult_1_r; symmetry  in |- *; apply Rmult_1_l.
red in |- *; generalize (rho_pos (vi intr)); intros; rewrite H7 in H6;
 elim (Rlt_irrefl 0 H6).
discrR.
apply Rlt_trans with (PI / 2)%R.
apply Rlt_1_PI2.
apply PI2_Rlt_PI.
rewrite D_F.
apply Rmult_le_pos.
left; apply TypeSpeed_pos.
apply cos_ge_0.
left; apply Rlt_le_trans with 0%R.
rewrite <- Ropp_0.
apply Ropp_lt_gt_contravar.
apply PI2_RGT_0.
unfold Rdiv in |- *; repeat simple apply Rmult_le_pos.
left; apply rho_pos.
assumption.
left; apply Rinv_0_lt_compat; prove_sup0.
left; apply Rlt_le_trans with 1%R.
apply Rmult_lt_reg_l with (2 / rho (vi intr))%R. 
unfold Rdiv in |- *; apply Rmult_lt_0_compat;
 [ prove_sup0 | apply Rinv_0_lt_compat; apply rho_pos ].
rewrite Rmult_1_r.
replace (2 / rho (vi intr) * (rho (vi intr) * (t / 2)))%R with t.
assumption.
unfold Rdiv in |- *.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm 2).
repeat rewrite <- Rmult_assoc.
rewrite <- Rinv_l_sym.
repeat rewrite Rmult_assoc.
rewrite <- Rinv_l_sym.
rewrite Rmult_1_r; rewrite Rmult_1_l.
reflexivity.
discrR.
red in |- *; generalize (rho_pos (vi intr)); intros; rewrite H5 in H4;
 elim (Rlt_irrefl 0 H4).
left; apply Rlt_1_PI2.
apply Rge_le.
assumption.
Qed.

Lemma G_0 : G 0 = 0%R.
unfold G in |- *; rewrite Rs_0; unfold Rminus, F in |- *; unfold Rdiv in |- *;
 rewrite Rmult_0_l; rewrite Rmult_0_r; rewrite sin_0;
 repeat rewrite Rmult_0_r; rewrite Rplus_0_l; apply Ropp_0.
Qed.

(**********)
Axiom
  G_pos :
    forall t : R, (0 <= t)%R -> (t < 2 / rho (vi intr))%R -> (0 <= G t)%R.

(**************************)
(******* THEOREM **********)
(**************************)

Theorem YCNGSTYS :
 forall t : R,
 (0 <= t)%R ->
 (rho (vi intr) * t < 2)%R ->
 (2 * r (vi intr) * sin (rho (vi intr) * (t / 2)) <=
  sqrt (Rsqr (xi intr t - xi intr 0) + Rsqr (yi intr t - yi intr 0)))%R.
intros; generalize (rho_pos (vi intr)); intro H1;
 generalize (Rinv_0_lt_compat (rho (vi intr)) H1); 
 intro H2;
 generalize (Rmult_lt_compat_l (/ rho (vi intr)) (rho (vi intr) * t) 2 H2 H0);
 intro H3; rewrite <- Rmult_assoc in H3; rewrite <- Rinv_l_sym in H3.
rewrite Rmult_1_l in H3; rewrite Rmult_comm in H3; generalize (G_pos t H H3);
 unfold G in |- *; intro H4;
 generalize (Rplus_le_compat_l (F t) 0 (Rs t - F t) H4); 
 rewrite Rplus_0_r; intro H5; unfold Rminus in H5;
 rewrite <- Rplus_assoc in H5; rewrite Rplus_comm in H5;
 rewrite <- Rplus_assoc in H5; rewrite Rplus_opp_l in H5;
 rewrite Rplus_0_l in H5; unfold Rs, F in H5; unfold r in |- *; 
 assumption.
red in |- *; intro H4; rewrite H4 in H1; elim (Rlt_irrefl 0 H1).
Qed.

End ycngstys.
