(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-2.1.html>         *)
(************************************************************************)

(* This file contains various properties of R that are not in the standard library. *)

Require Import Reals.
Require Import Lra.
Require Import Fourier.
Require Import Euclid. 
Require Import Omega.

Lemma Rlt_stepl:forall x y z, Rlt x y -> x=z -> Rlt z y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Lemma Rlt_stepr:forall x y z, Rlt x y -> y=z -> Rlt x z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Declare Left Step Rlt_stepl.
Declare Right Step Rlt_stepr.


Lemma Rle_stepl:forall x y z, Rle x y -> x=z -> Rle z y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Lemma Rle_stepr:forall x y z, Rle x y -> y=z -> Rle x z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Declare Left Step Rle_stepl.
Declare Right Step Rle_stepr.


Lemma Rneq_stepl:forall x y z:R, x<>y -> x=z -> z<>y.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Lemma Rneq_stepr:forall x y z:R, x<>y -> y=z -> x<>z.
Proof.
 intros x y z H_lt H_eq; subst; assumption.
Defined.

Declare Left Step Rneq_stepl.
Declare Right Step Rneq_stepr.


Lemma Rlt_zero_Rminus : forall r1 r2:R , 0 < r1-r2  -> r2 < r1.
Proof.
 intros r1 r2 H; apply Rminus_lt; apply Ropp_lt_cancel; rewrite Ropp_minus_distr; rewrite Ropp_0; assumption.
Qed.

Lemma Rle_zero_Rminus : forall r1 r2:R , 0 <= r1-r2  -> r2 <= r1.
Proof.
 intros r1 r2 H; apply RIneq.Rminus_le; apply RIneq.Ropp_le_cancel;rewrite RIneq.Ropp_minus_distr; rewrite RIneq.Ropp_0; assumption.
Qed.

Lemma Rle_Rminus_zero : forall r1 r2:R , r2 <= r1 -> 0 <= r1-r2.
Proof.
 intros r1 r2 H; lra.
Qed.

Lemma Rlt_Rminus_zero : forall r1 r2:R , r2 < r1 -> 0 < r1-r2.
Proof.
 intros r1 r2 H; lra.
Qed.

Lemma Rlt_not_eq': forall r1 r2 : R, r1 < r2 -> r2 <> r1.
Proof.
 intros r1 r2 H; apply sym_not_eq; apply Rlt_not_eq; assumption.
Qed.

Lemma Rmult_reg_nonzero_r: forall r1 r2 : R, r1 * r2 <> 0 -> r2 <> 0.
Proof.
 intros r1 r2 H_r12 H_false; apply H_r12; subst r2; ring.
Qed.
 
Lemma Rmult_reg_nonzero_l: forall r1 r2 : R, r1 * r2 <> 0 -> r1 <> 0.
Proof.
 intros r1 r2 H_r12 H_false; apply H_r12; subst r1; ring.
Qed.

Lemma Rlt_Ropp_pos: forall r : R, r < 0 -> 0 < - r.
Proof.
 intros r Hr; lra.
Qed.

Lemma Rlt_mult_neg_neg: forall r1 r2 : R, r1<0 -> r2<0 -> 0 < r1 * r2.
Proof.
 intros r1 r2 Hr1 Hr2; stepr ((-r1)*(-r2)); [|ring]; apply Rmult_lt_0_compat; lra. 
Qed.

Definition Rinv_pos:= Rinv_0_lt_compat.
Definition Rle_mult_nonneg_nonneg:=Rmult_le_pos.
Definition Rlt_mult_pos_pos:=Rmult_lt_0_compat.
Definition Rmult_resp_nonzero:=RIneq.prod_neq_R0.
Definition Rinv_resp_nonzero:=Rinv_neq_0_compat.
Definition Ropp_resp_nonzero:=RIneq.Ropp_neq_0_compat.


Hint Resolve Rlt_Ropp_pos Rinv_pos R1_neq_R0 Rle_mult_nonneg_nonneg
             Rlt_mult_pos_pos Rlt_mult_neg_neg Rlt_not_eq' Rlt_not_eq
             Rmult_resp_nonzero Rinv_resp_nonzero Ropp_resp_nonzero.

Lemma Rmult_mult_nonneg: forall r, 0<=r*r.
Proof.
 intros r; stepr (Rsqr r); trivial; apply Rle_0_sqr.
Qed.

Lemma Rmult_mult_Ropp_nonpos: forall r, -(r*r)<=0.
Proof.
 intros r; generalize (r*r) (Rmult_mult_nonneg r); clear r; intros; lra.
Qed.

Lemma Rlt_mult_pos_neg: forall r1 r2 : R, r1 < 0 -> 0<r2 -> r1 * r2<0.
Proof.
 intros r1 r2 Hr1 Hr2; apply Ropp_lt_cancel; stepl R0; [|ring]; stepr ((-r1)*r2); [|ring]; apply Rlt_mult_pos_pos; auto.
Qed.

Lemma Rlt_mult_neg_pos: forall r1 r2 : R, 0<r1 -> r2<0 -> r1 * r2<0.
Proof.
 intros r1 r2 Hr1 Hr2; apply Ropp_lt_cancel; stepl R0; [|ring]; stepr (r1*(-r2)); [|ring]; apply Rlt_mult_pos_pos; auto.
Qed.

Lemma Rdiv_Rmult_pos_neg_Rle: forall x y z t, R0 < z -> t < R0 -> x / z <= y / t -> y * z <= x * t.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_neg_pos; assumption.
Qed.

Lemma Rdiv_Rmult_pos_neg_Rle': forall x y z t, R0 < z -> t < R0 -> x / z <= y / t -> z*y <= t*x.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_neg_pos; assumption.
Qed.

Lemma Rdiv_Rmult_neg_pos_Rle: forall x y z t, z<0 -> 0<t -> x / z <= y / t -> y * z <= x * t.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_neg_pos_Rle': forall x y z t, z<0 -> 0<t -> x / z <= y / t -> z*y <= t*x.
Proof.
 intros x y z t Hz Ht Hxyzt; stepl ((z*t)*(y/t)); [|field; auto]; stepr ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_neg_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_neg_neg_Rle: forall x y z t, z<0 -> t<0 -> x / z <= y / t -> x * t<=y * z.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_neg_neg_Rle': forall x y z t, z<0 -> t<0 -> x / z <= y / t -> t*x<=z*y.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_pos_pos_Rle: forall x y z t, 0<z -> 0<t -> x / z <= y / t -> x * t<=y * z.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.

Lemma Rdiv_Rmult_pos_pos_Rle': forall x y z t, 0<z -> 0<t -> x / z <= y / t -> t*x<=z*y.
Proof.
 intros x y z t Hz Ht Hxyzt; stepr ((z*t)*(y/t)); [|field; auto]; stepl ((z*t)*(x/z)); [|field; auto];
 apply Rmult_le_compat_l; auto; apply Rlt_le; auto; apply Rlt_mult_pos_neg; assumption.
Qed.


Lemma Rdiv_Ropp_numerator: forall x y, y <> R0 -> (- x / y = - (x / y))%R.
Proof.
 intros x y Hy; field; trivial.
Qed.

Lemma Rdiv_Ropp_denomintor: forall x y, y <> R0 -> (x / - y = - (x / y))%R. 
 intros x y Hy; field; trivial.  
Qed.

Lemma Rdiv_Rmult_numerator: forall (x y z:R), y<>R0 -> (z*(x/y)=(z*x)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rdiv_Rmult_numerator_r: forall (x y z:R), y<>R0 -> ((x/y)*z=(x*z)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rdiv_Rplus_Rmult: forall (x y z:R), y<>R0 -> (x/y + z = (x+y*z)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rdiv_Rminus_Rmult: forall x y z, y<>R0 -> (x/y - z = (x-y*z)/y)%R.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rminus_Rdiv_Rmult: forall x y z, ~(y=R0)->(z-x/y=(y*z-x)/y)%R.
Proof.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rplus_Rdiv_Rmult: forall x y z, ~(y=R0)->(z+x/y=(y*z+x)/y)%R.
Proof.
Proof.
 intros x y z Hy; field; auto.
Qed.

Lemma Rminus_Rdiv:forall x y z t, z<>R0 -> t<>R0 -> (x/z - y/t = (x*t-y*z)/(z*t))%R.
Proof.
 intros x y z t Hz Ht; field; split; trivial.
Defined.

Lemma Rplus_Rdiv:forall x y z t, z<>R0 -> t<>R0 -> (x/z + y/t = (x*t+y*z)/(z*t))%R.
Proof.
 intros x y z t Hz Ht; field; split; trivial. 
Defined.

Lemma Ropp_mult_distr: forall r1 r2 : R, - (r1 * r2) = (- r1 * r2).
Proof.
 intros r1 r2; ring.
Qed.

Lemma Rle_pos_nonneg_Rmult: forall r1 r2 : R, 0 < r1 ->  0 <= r2 * r1 -> 0<= r2.
Proof.
 intros r1 r2 Hr2 Hr12; stepr ((r2*r1)*/r1); try field; auto; apply (Rle_mult_inv_pos _ _ Hr12 Hr2).
Qed.

Lemma Rle_pos_nonneg_Rdiv: forall r1 r2 : R, 0 < r1 ->  0 <= r2 / r1 -> 0<= r2.
Proof.
 intros r1 r2 Hr2 Hr12; unfold Rdiv in Hr12; apply Rle_pos_nonneg_Rmult with (/r1); auto.
Qed.

Lemma Rle_mult_nonpos_nonpos: forall r1 r2 : R, r1<=0 -> r2<=0 -> 0 <= r1 * r2.
Proof.
 intros r1 r2 Hr1 Hr2; stepr ((-r1)*(-r2)); [|ring]; apply Rle_mult_nonneg_nonneg; lra. 
Qed.

Lemma Rlt_pos_pos_Rmult: forall r1 r2 : R, 0 < r1 ->  0 < r2 * r1 -> 0< r2.
Proof.
 intros r1 r2 Hr2 Hr12; stepr ((r2*r1)*/r1); try field; auto; apply (Rle_mult_inv_pos _ _ Hr12 Hr2).
Qed.

Lemma Rlt_pos_pos_Rdiv: forall r1 r2 : R, 0 < r1 ->  0 < r2 / r1 -> 0< r2.
Proof.
 intros r1 r2 Hr2 Hr12; unfold Rdiv in Hr12; apply Rlt_pos_pos_Rmult with (/r1); auto.
Qed.

Lemma Rdiv_Rdiv_simplify: forall x y z : R, z <> R0 -> y <> R0 -> x / z / (y / z) = x / y.
Proof.
 intros x y z Hz Hy; field; auto.
Qed.

Definition Rmult_reg_l := RIneq.Rmult_eq_reg_l.

Lemma Rmult_reg_r : forall r r1 r2 : R, r1 * r = r2 * r -> r <> 0 -> r1 = r2.
Proof.
  intros x y z; rewrite (Rmult_comm z x); rewrite (Rmult_comm y x); exact (Rmult_reg_l x y z).
Qed.

Lemma Rmult_Rdiv: forall x y z t : R, z <> R0 -> t <> R0 -> x * t = y * z -> x / z = y / t.
Proof.
 intros x y z t Hz Ht Hxtyz;
 apply Rmult_reg_l with (z*t); auto;
 transitivity (x*t);
 [|transitivity (y*z); trivial]; field; trivial.
Qed.

Lemma Rmult_Rdiv_pos_Rle: forall x y z t, (R0 < z)%R -> (R0 < t)%R -> (x * t <= y * z)%R -> (x / z <= y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rle_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Rle_mult_inv_pos; auto;
 apply Rle_Rminus_zero; assumption. 
Qed.

Lemma Rmult_Rdiv_neg_Rle: forall x y z t, (z < R0)%R -> (t < R0)%R -> (x * t <= y * z)%R -> (x / z <= y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rle_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Rle_mult_inv_pos; auto;
 apply Rle_Rminus_zero; assumption. 
Qed.

Lemma Rdiv_Rmult_simplify: forall x y z : R, z <> 0%R -> y <> 0%R -> (x * z / (y * z))%R = (x / y)%R.
Proof.
 intros; field; auto.
Qed.

Lemma Rdiv_Rmult_numerator_denominator: forall x y z t: R, t <> 0%R -> y <> 0%R -> ((x/y)*(z/t))%R=((x*z)/(y*t))%R.
Proof.
 intros; field; auto.
Qed.

Lemma Rdiv_Rdiv_Rmult_numerator: forall x y z : R, y <> 0 -> z <> 0 -> (x / y / z) = (x / (y * z)).
Proof.
 intros x y z Hy Hz; field; split; trivial. 
Qed.

Lemma Rdiv_Rdiv_Rmult_denominator: forall x y z : R, y <> 0 -> z <> 0 -> (x / (y / z)) = (x*z / y ).
Proof.
 intros x y z Hy Hz; field; auto. 
Qed.

Lemma Rmult_Rdiv_pos_Rlt: forall x y z t, (R0 < z)%R -> (R0 < t)%R -> (x * t < y * z)%R -> (x / z < y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rlt_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto;
 apply Rlt_Rminus_zero; assumption. 
Qed.

Lemma Rmult_Rdiv_neg_Rlt: forall x y z t, (z < R0)%R -> (t < R0)%R -> (x * t < y * z)%R -> (x / z < y / t)%R.
Proof.
 intros x y z t Hz Ht Hxtys;
 apply Rlt_zero_Rminus;
 rewrite Rminus_Rdiv; auto;
 unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto;
 apply Rlt_Rminus_zero; assumption. 
Qed.

Lemma Rlinear_non_zero_1:forall a b x y, (y<>0)%R -> (a*x+b*y<>0)%R -> (a*(x/y)+b<>0)%R.
Proof.
 intros a b x y Hy Habxy.
 stepl (/y*(a*x+b*y))%R; auto; field; auto.
Qed.

Lemma Rlinear_non_zero_2:forall a b x y, (y<>0)%R -> (a*(x/y)+b<>0)%R -> (a*x+b*y<>0)%R.
Proof.
 intros a b x y Hy Habxy.
 stepl (y*(a*(x/y)+b))%R; auto; field; auto.
Qed.
 
Lemma Rlinear_non_zero_3: forall a b x : R, a <> 0 -> x <> -b/a -> a * x + b <> 0.
Proof.
 intros a b x Ha Hx.
 generalize (Rminus_eq_contra _ _ Hx); clear Hx; intros Hx.
 stepl (a*(x+(b/a))); [apply Rmult_resp_nonzero|field]; trivial.  
 stepl (x - - b / a); trivial; field; trivial.
Qed.

Lemma Rbilinear_non_zero_2:forall a b c d x y x' y', y<>0 -> y'<>0 -> 
   (a*(x/y)*(x'/y')+b*(x/y)+c*(x'/y')+d<>0)%R -> (a*x*x'+b*x*y'+c*y*x'+d*y*y'<>0)%R.
Proof.
 intros a b c d x y x' y' Hy Hy' Habxy;
 stepl ((y*y')*(a*(x/y)*(x'/y')+b*(x/y)+c*(x'/y')+d))%R; auto; field; auto.
Qed.

Lemma Rle_dec_weak:forall (x y:R), {Rle x y}+{(Rle y x)}.
Proof.
 intros x y; case (Rlt_le_dec x y); intros; [ left | right ]; trivial; apply Rlt_le; trivial.
Defined.

Lemma Rtrichotomy_inf:forall r1 r2 : R, {(r1 < r2)%R} + {r1 = r2} + {(r2<r1)%R}.
Proof.
 intros r1 r2; elim (total_order_T r1 r2); intros ;auto.
Qed.

Lemma not_O_S_INR: forall n : nat, INR (S n) <> 0%R.
Proof.
 intros n; apply not_O_INR; auto with arith.
Qed.

Lemma pos_S_INR: forall n : nat, (0 < INR (S n))%R.
Proof.
 intros n; apply lt_INR_0; auto with arith.  
Qed.

Hint Resolve not_O_S_INR pos_S_INR pos_INR.


Lemma Req_Rdiv_Rone:forall x y, y<>0 -> x=y -> x/y =1.
Proof.
 intros x y Hy Hxy; subst x; unfold Rdiv; apply Rinv_r; trivial.
Qed.

Lemma Req_Ropp_Rdiv_minus_Rone:forall x y, y<>0 -> x=-y -> x/y =-1.
Proof.
 intros x y Hy Hxy; subst x; unfold Rdiv; field; assumption.
Qed.

Lemma Rmax_involutive: forall q, Rmax q q = q.
Proof.
 intros q; unfold Rmax; destruct (Rle_dec q q); trivial.
Qed.

Lemma Rabs_Rle: forall q p : R, (- p <= q)%R -> (q <= p)%R -> (Rabs q <= p)%R.
Proof.
 intros q p H1 H2; assert (H_p: 0<= p); [lra|];
 stepr (Rmax (Rabs (-p)) (Rabs p));
 [ apply RmaxAbs; trivial
 | rewrite Rabs_Ropp; rewrite Rmax_involutive; apply Rabs_pos_eq; assumption].
Qed.

Lemma Rabs_Rle_1: forall q, (- 1 <= q)%R -> (q <= 1)%R -> (Rabs q <= 1)%R.
Proof.
 intros q H1 H2; apply Rabs_Rle; trivial.
Qed.

Lemma pow_Rle_r : forall (x y : R) (n : nat),  - x <= y -> y <= x -> pow y n <= pow x n.
Proof.
 intros x y n H1 H2; apply pow_maj_Rabs; apply Rabs_Rle; assumption.
Qed.


Lemma pow_Rle_r_1 : forall (y: R) (n : nat),  - 1 <= y -> y <= 1 -> pow y n <= 1.
Proof.
 intros y n H1 H2; rewrite <- pow1 with n; apply pow_Rle_r; assumption.
Qed.

Lemma pow_even_nonneg:forall (y: R) (n : nat), 0 <= pow y (2*n)%nat.
Proof.
 induction n; simpl.
  auto with real.
  replace (n + S (n + 0))%nat with (S (2*n)%nat); [|omega].
  simpl.
  stepr ((y*y)*(pow y (2*n)%nat)); [|simpl;ring].
  apply Rle_mult_nonneg_nonneg; [apply Rmult_mult_nonneg|apply IHn].
Qed.

Lemma pow_Rle_l_1 : forall (y: R) (n : nat),  - 1 <= y -> y <= 1 -> -1 <= pow y n.
Proof.
 intros y n.
 assert (H2:(2 > 0)%nat); [omega|].
 destruct (modulo 2 H2 n) as [[|[|r]] [k [Hk1 Hk2]]]; intros hyp1 hyp2.
 3: inversion Hk2; inversion H0; contradict H3;auto with arith.
  rewrite Hk1.
  replace (k * 2 + 0)%nat with (2*k)%nat; [|omega].
  apply Rle_trans with 0; [ lra | apply pow_even_nonneg].

  rewrite Hk1.
  replace (k * 2 + 1)%nat with (S(2*k)%nat);[|omega].
  generalize (pow_even_nonneg y k).
  simpl.
  intros hyp3.
  destruct (Rtrichotomy_inf y 0) as [[H|H]|H].
   apply Rle_trans with (- (pow y (k + (k + 0)))).
    apply Ropp_le_contravar; apply pow_Rle_r_1; assumption.
    stepl ((-1)  * (pow y (k + (k + 0)))); [apply Rmult_le_compat_r; assumption|ring].

   subst y; stepr 0; [lra |ring].
   stepr (pow y (S(2*k)%nat)); trivial.
   apply Rle_trans with 0;[|apply pow_le]; lra.
Qed.

Lemma conjL_range_l:forall r, -1 <= r -> -1<= (r-1)/(r+3).
Proof.
 intros r Hr;
 stepl (-1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle; try lra;
 rewrite Rmult_plus_distr_l; rewrite Rmult_1_r; lra.
Qed.

Lemma conjL_range_r:forall r, -1<=r -> r <= 1 -> (r-1)/(r+3) <= 0.
Proof.
 intros r Hr1 Hr2;
 apply Ropp_le_cancel; stepl 0; try ring;
 unfold Rdiv; rewrite Ropp_mult_distr;
 apply Rle_mult_inv_pos; lra.
Qed.

Lemma conjL_range_weak:forall r, -1 <= r <= 1-> -1<= (r-1)/(r+3)<=1.
Proof.
 intros r [Hr1 Hr2]; split.
 apply conjL_range_l; trivial.
 apply Rle_trans with 0; try lra; apply conjL_range_r; trivial.
Qed.


Lemma conjR_range_l:forall r, -1 <= r -> r <= 1 -> 0<= (r+1)/(-r+3).
Proof.
 intros r Hr1 Hr2;
 unfold Rdiv; apply Rle_mult_inv_pos; lra.
Qed.

Lemma conjR_range_r:forall r, r <= 1 -> (r+1)/(-r+3)<=1.
Proof.
 intros r Hr;
 stepr (1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle;  try lra;
 rewrite Rmult_1_r;  rewrite Rmult_1_l; lra.
Qed.

Lemma conjR_range_weak:forall r, -1 <= r <= 1-> -1<= (r+1)/(-r+3)<=1.
Proof.
 intros r [Hr1 Hr2]; split.
 apply Rle_trans with 0; try lra; apply conjR_range_l; trivial.
 apply conjR_range_r; trivial.
Qed.


Lemma conjM_range_l:forall r, -1 <= r -> -1/3<= r/3.
Proof.
 intros r Hr; lra.
Qed.

Lemma conjM_range_r:forall r, r <= 1 -> r/3<=1/3.
Proof.
 intros r Hr; lra.
Qed.


Lemma conjM_range_weak:forall r, -1 <= r <= 1-> -1<= r/3 <=1.
Proof.
 intros r [Hr1 Hr2]; split.
 apply Rle_trans with (-1/3); try lra; apply conjM_range_l; trivial.
 apply Rle_trans with (1/3); try lra; apply conjM_range_r; trivial.
Qed.


Lemma conjLinv_range_r:forall r, r <= 0 -> (3*r+1)/(-r+1)<=1.
Proof.
 intros r Hr;
 stepr (1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle;  try lra;
 rewrite Rmult_1_r;  rewrite Rmult_1_l; lra.
Qed.


Lemma conjLinv_range_l:forall r, -1<=r -> r <= 0 -> -1<=(3*r+1)/(-r+1).
Proof.
 intros r Hr1 Hr2;
 stepl (-(1)/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle; try lra;
 rewrite Rmult_plus_distr_l; do 2 rewrite Rmult_1_r; rewrite Rmult_opp_opp; lra.
Qed.

Lemma conjRinv_range_r:forall r, 0<=r-> r <= 1 -> (3*r-1)/(r+1)<=1.
Proof.
 intros r Hr1 Hr2.
 stepr (1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle;  try lra;
 rewrite Rmult_1_r;  rewrite Rmult_1_l; lra.
Qed.

Lemma conjRinv_range_l:forall r, 0<=r -> -1<=(3*r-1)/(r+1).
Proof.
 intros r Hr;
 stepl (-1/1); [| field; apply R1_neq_R0];
 apply Rmult_Rdiv_pos_Rle; lra.
Qed.

Lemma conjMinv_range_r:forall r, r <= 1/3 -> 3*r<=1.
Proof.
 intros r Hr; lra.
Qed.

Lemma conjMinv_range_l:forall r, -1/3<=r -> -1<=3*r.
Proof.
 intros r Hr; lra.
Qed.


Lemma CV_const:  forall const, Un_cv (fun i : nat => const) const.
Proof.
 intros const eps H_eps; exists 0%nat; intros n _; rewrite Rfunctions.R_dist_eq; trivial. 
Qed.

Lemma CV_shift_S' : forall Un l,  Un_cv (fun n => Un (S n)) l -> Un_cv Un l.
Proof. 
 intros Un l; unfold Un_cv; intros H_lim eps H_eps.
 destruct (H_lim eps H_eps) as [N H_N].
 exists (S N).
 intros [|n] H_n.
  red in H_n; apply False_ind; apply (le_Sn_O _ H_n).
  apply H_N; red; apply le_S_n; trivial.
Qed.

Lemma CV_shift_S : forall Un l,  Un_cv Un l -> Un_cv (fun n => Un (S n)) l.
Proof. 
 intros Un l; unfold Un_cv; intros H_lim eps H_eps.
 destruct (H_lim eps H_eps) as [N H_N].
 exists (S N).
 intros [|n] H_n.
  red in H_n; apply False_ind; apply (le_Sn_O _ H_n).
  apply H_N; red; apply le_trans with n. 
   apply le_S_n; trivial.
   repeat constructor.
Qed.

Lemma CV_extensionality : forall Un Un', (forall n, Un n = Un' n) ->  forall l, Un_cv Un l -> Un_cv Un' l.
Proof.
 intros Un Un' H_ext l.
 unfold Un_cv; intros H_lim eps H_eps.
 destruct (H_lim eps H_eps) as [N H_N].
 exists N.
 intros n H_n'.
 rewrite <- (H_ext n); apply H_N; trivial.
Qed.

Ltac ring_exact_R hyp := 
 match type of hyp with 
 | Rlt ?X1 ?X2 => (stepr X2; trivial; ring) || (stepl X1; trivial; ring)
 | Rle ?X1 ?X2 => (stepr X2; trivial; ring) || (stepl X1; trivial; ring)
 | ~(@eq R ?X1 ?X2) => (stepr X2; trivial; ring) || (stepl X1; trivial; ring)
 | ?X3 => fail 1
 end.
