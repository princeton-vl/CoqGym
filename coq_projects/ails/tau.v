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
Require Import ails_def.
Require Import trajectory_const.

Unset Standard Proposition Elimination Names.

(**********)
Definition dx (intruder evader : State) (t : R) : R :=
  (xt intruder + t * intruderSpeed * cosd (heading intruder) -
   (xt evader + t * evaderSpeed))%R.
Definition dy (intruder evader : State) (t : R) : R :=
  (yt intruder + t * intruderSpeed * sind (heading intruder) - yt evader)%R.
Definition dxdt (intruder : State) : R :=
  (intruderSpeed * cosd (heading intruder) - evaderSpeed)%R.
Definition dydt (intruder : State) : R :=
  (intruderSpeed * sind (heading intruder))%R.
Definition RR (intruder evader : State) (t : R) : R :=
  sqrt (Rsqr (dx intruder evader t) + Rsqr (dy intruder evader t)).
Definition div_tau (intruder evader : State) : R :=
  (Rsqr (dxdt intruder) + Rsqr (dydt intruder))%R.

(**********)
Lemma Req_EM_var : forall r1 r2 : R, {r1 = r2} + {r1 <> r2}. 
intros; elim (total_order_T r1 r2); intros.
elim a; intro.
right; red in |- *; intro; rewrite H in a0; elim (Rlt_irrefl r2 a0). 
left; assumption.
right; red in |- *; intro.
rewrite H in b; elim (Rlt_irrefl r2 b).
Qed. 

(***********)
Definition tau (intruder evader : State) (t : R) : R :=
  match Req_EM_var (div_tau intruder evader) 0 with
  | left _ => 0%R
  | right _ =>
      (-
       (dx intruder evader t * dxdt intruder +
        dy intruder evader t * dydt intruder) / div_tau intruder evader)%R
  end.  
Definition tmin (intruder evader : State) : R :=
  match Req_EM_var (div_tau intruder evader) 0 with
  | left _ => 0%R
  | right _ =>
      (-
       (dxdt intruder * (xt intruder - xt evader) +
        dydt intruder * (yt intruder - yt evader)) / 
       div_tau intruder evader)%R
  end.

(**********)
Lemma tau_tmin :
 forall (intruder evader : State) (t : R),
 div_tau intruder evader <> 0%R ->
 tau intruder evader t = (tmin intruder evader - t)%R.
intros.
cut
 (tau intruder evader t =
  (-
   (dx intruder evader t * dxdt intruder +
    dy intruder evader t * dydt intruder) / div_tau intruder evader)%R).
cut
 (tmin intruder evader =
  (-
   (dxdt intruder * (xt intruder - xt evader) +
    dydt intruder * (yt intruder - yt evader)) / div_tau intruder evader)%R).
intros.
rewrite H0; rewrite H1.
unfold Rdiv in |- *.
replace
 (-
  (dxdt intruder * (xt intruder - xt evader) +
   dydt intruder * (yt intruder - yt evader)) * / div_tau intruder evader - t)%R
 with
 (-
  (dxdt intruder * (xt intruder - xt evader + t * dxdt intruder) +
   dydt intruder * (yt intruder - yt evader + t * dydt intruder)) /
  div_tau intruder evader)%R.
cut ((xt intruder - xt evader + t * dxdt intruder)%R = dx intruder evader t).
cut ((yt intruder - yt evader + t * dydt intruder)%R = dy intruder evader t).
intros; rewrite H2; rewrite H3; unfold Rdiv in |- *;
 rewrite (Rmult_comm (dx intruder evader t));
 rewrite (Rmult_comm (dy intruder evader t)); reflexivity.
unfold dydt, dy in |- *; ring.
unfold dxdt, dx in |- *; ring.
unfold Rdiv in |- *; apply (Rmult_eq_reg_l (div_tau intruder evader)).
rewrite (Rmult_comm (div_tau intruder evader)); repeat rewrite Rmult_assoc;
 rewrite <- Rinv_l_sym.
rewrite Rmult_1_r; rewrite (Rmult_comm (div_tau intruder evader));
 replace
  ((-
    (dxdt intruder * (xt intruder - xt evader) +
     dydt intruder * (yt intruder - yt evader)) * / div_tau intruder evader -
    t) * div_tau intruder evader)%R with
  (-
   (dxdt intruder * (xt intruder - xt evader) +
    dydt intruder * (yt intruder - yt evader)) * / div_tau intruder evader *
   div_tau intruder evader - t * div_tau intruder evader)%R.
repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
rewrite Rmult_1_r; unfold div_tau in |- *; unfold Rsqr in |- *; ring.
assumption.
symmetry  in |- *; unfold Rminus in |- *;
 replace
  (-
   (dxdt intruder * (xt intruder + - xt evader) +
    dydt intruder * (yt intruder + - yt evader)) * 
   / div_tau intruder evader + - t)%R with
  (-
   (dxdt intruder * (xt intruder + - xt evader) +
    dydt intruder * (yt intruder + - yt evader)) * 
   / div_tau intruder evader + - t)%R.
replace (- (t * div_tau intruder evader))%R with
 (- t * div_tau intruder evader)%R.
replace
 (-
  (dxdt intruder * (xt intruder + - xt evader) +
   dydt intruder * (yt intruder + - yt evader)) * / div_tau intruder evader *
  div_tau intruder evader)%R with
 (-
  (dxdt intruder * (xt intruder + - xt evader) +
   dydt intruder * (yt intruder + - yt evader)) * / div_tau intruder evader *
  div_tau intruder evader)%R.
apply Rmult_plus_distr_r.
ring.
ring.
ring.
assumption.
assumption.
unfold tmin in |- *; case (Req_EM_var (div_tau intruder evader) 0); intro.
rewrite e in H; elim H; reflexivity.
reflexivity.
unfold tau in |- *; case (Req_EM_var (div_tau intruder evader) 0); intro.
rewrite e in H; elim H; reflexivity.
reflexivity.
Qed.

(**********)
Definition Ax2_R (intruder : State) : R :=
  (Rsqr (sind (heading intruder) * intruderSpeed) +
   Rsqr (- evaderSpeed + cosd (heading intruder) * intruderSpeed))%R.

(**********)
Lemma Ax2_R_pos : forall intruder : State, (0 <= Ax2_R intruder)%R.
intro; unfold Ax2_R in |- *; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(**********)
Definition Bx_R (intruder evader : State) : R :=
  (-2 * (yt evader * sind (heading intruder) * intruderSpeed) +
   2 * (yt intruder * sind (heading intruder) * intruderSpeed) -
   2 * (cosd (heading intruder) * xt evader * intruderSpeed) +
   2 * (cosd (heading intruder) * xt intruder * intruderSpeed) +
   2 * (xt evader * evaderSpeed) - 2 * (xt intruder * evaderSpeed))%R.

Definition C_R (intruder evader : State) : R :=
  (Rsqr (yt intruder - yt evader) + Rsqr (xt intruder - xt evader))%R.

(**********)
Lemma Rsqr_R :
 forall (intruder evader : State) (t : R),
 Rsqr (RR intruder evader t) =
 (Ax2_R intruder * Rsqr t + Bx_R intruder evader * t + C_R intruder evader)%R.
intros; unfold RR in |- *; unfold dx, dy in |- *; rewrite Rsqr_sqrt;
 [ replace
    (xt intruder + t * intruderSpeed * cosd (heading intruder) -
     (xt evader + t * evaderSpeed))%R with
    ((- evaderSpeed + cosd (heading intruder) * intruderSpeed) * t +
     (xt intruder - xt evader))%R;
    [ replace
       (yt intruder + t * intruderSpeed * sind (heading intruder) - yt evader)%R
       with
       (sind (heading intruder) * intruderSpeed * t +
        (yt intruder - yt evader))%R;
       [ repeat rewrite Rsqr_plus; repeat rewrite Rsqr_mult;
          unfold Ax2_R in |- *;
          apply
           Rplus_eq_reg_l
            with
              (-
               (Rsqr (sind (heading intruder) * intruderSpeed) +
                Rsqr
                  (- evaderSpeed + cosd (heading intruder) * intruderSpeed)) *
               Rsqr t)%R;
          replace
           (-
            (Rsqr (sind (heading intruder) * intruderSpeed) +
             Rsqr (- evaderSpeed + cosd (heading intruder) * intruderSpeed)) *
            Rsqr t +
            (Rsqr (- evaderSpeed + cosd (heading intruder) * intruderSpeed) *
             Rsqr t + Rsqr (xt intruder - xt evader) +
             2 *
             ((- evaderSpeed + cosd (heading intruder) * intruderSpeed) * t) *
             (xt intruder - xt evader) +
             (Rsqr (sind (heading intruder)) * Rsqr intruderSpeed * Rsqr t +
              Rsqr (yt intruder - yt evader) +
              2 * (sind (heading intruder) * intruderSpeed * t) *
              (yt intruder - yt evader))))%R with
           (Rsqr (xt intruder - xt evader) +
            2 *
            ((- evaderSpeed + cosd (heading intruder) * intruderSpeed) * t) *
            (xt intruder - xt evader) + Rsqr (yt intruder - yt evader) +
            2 * (sind (heading intruder) * intruderSpeed * t) *
            (yt intruder - yt evader))%R;
          [ replace
             (-
              (Rsqr (sind (heading intruder) * intruderSpeed) +
               Rsqr (- evaderSpeed + cosd (heading intruder) * intruderSpeed)) *
              Rsqr t +
              ((Rsqr (sind (heading intruder) * intruderSpeed) +
                Rsqr
                  (- evaderSpeed + cosd (heading intruder) * intruderSpeed)) *
               Rsqr t + Bx_R intruder evader * t + 
               C_R intruder evader))%R with
             (Bx_R intruder evader * t + C_R intruder evader)%R;
             [ unfold C_R in |- *;
                apply
                 Rplus_eq_reg_l
                  with
                    (-
                     (Rsqr (yt intruder - yt evader) +
                      Rsqr (xt intruder - xt evader)))%R;
                replace
                 (-
                  (Rsqr (yt intruder - yt evader) +
                   Rsqr (xt intruder - xt evader)) +
                  (Rsqr (xt intruder - xt evader) +
                   2 *
                   ((- evaderSpeed + cosd (heading intruder) * intruderSpeed) *
                    t) * (xt intruder - xt evader) +
                   Rsqr (yt intruder - yt evader) +
                   2 * (sind (heading intruder) * intruderSpeed * t) *
                   (yt intruder - yt evader)))%R with
                 (2 *
                  ((- evaderSpeed + cosd (heading intruder) * intruderSpeed) *
                   t) * (xt intruder - xt evader) +
                  2 * (sind (heading intruder) * intruderSpeed * t) *
                  (yt intruder - yt evader))%R;
                [ replace
                   (-
                    (Rsqr (yt intruder - yt evader) +
                     Rsqr (xt intruder - xt evader)) +
                    (Bx_R intruder evader * t +
                     (Rsqr (yt intruder - yt evader) +
                      Rsqr (xt intruder - xt evader))))%R with
                   (Bx_R intruder evader * t)%R;
                   [ unfold Bx_R in |- *; ring | ring ]
                | ring ]
             | ring ]
          | rewrite (Rsqr_mult (sind (heading intruder)) intruderSpeed); ring ]
       | ring ]
    | ring ]
 | apply Rplus_le_le_0_compat; apply Rle_0_sqr ].
Qed.

(**********)
Definition Rsqr_Rmin (intruder evader : State) : R :=
  match Req_EM_var (Ax2_R intruder) 0 with
  | left _ => 0%R
  | right _ =>
      ((4 * Ax2_R intruder * C_R intruder evader -
        Rsqr (Bx_R intruder evader)) / (4 * Ax2_R intruder))%R
  end.

(**********)
Lemma tmin_0 :
 forall intruder evader : State,
 div_tau intruder evader <> 0%R ->
 tmin intruder evader = (- Bx_R intruder evader / (2 * Ax2_R intruder))%R.
intros; unfold tmin in |- *; case (Req_EM_var (div_tau intruder evader) 0);
 intro.
elim H; assumption.
unfold div_tau, Bx_R, Ax2_R in |- *; unfold dxdt, dydt in |- *;
 unfold Rdiv in |- *; rewrite Rinv_mult_distr.
replace
 (Rsqr (sind (heading intruder) * intruderSpeed) +
  Rsqr (- evaderSpeed + cosd (heading intruder) * intruderSpeed))%R with
 (Rsqr (intruderSpeed * cosd (heading intruder) - evaderSpeed) +
  Rsqr (intruderSpeed * sind (heading intruder)))%R.
apply
 Rmult_eq_reg_l
  with
    (Rsqr (intruderSpeed * cosd (heading intruder) - evaderSpeed) +
     Rsqr (intruderSpeed * sind (heading intruder)))%R.
rewrite
 (Rmult_comm
    (Rsqr (intruderSpeed * cosd (heading intruder) - evaderSpeed) +
     Rsqr (intruderSpeed * sind (heading intruder))))
 ; repeat rewrite Rmult_assoc;
 rewrite <-
  (Rinv_l_sym
     (Rsqr (intruderSpeed * cosd (heading intruder) - evaderSpeed) +
      Rsqr (intruderSpeed * sind (heading intruder))))
  .
rewrite Rmult_1_r;
 rewrite
  (Rmult_comm
     (Rsqr (intruderSpeed * cosd (heading intruder) - evaderSpeed) +
      Rsqr (intruderSpeed * sind (heading intruder))))
  ; repeat rewrite Rmult_assoc;
 rewrite <-
  (Rinv_l_sym
     (Rsqr (intruderSpeed * cosd (heading intruder) - evaderSpeed) +
      Rsqr (intruderSpeed * sind (heading intruder))))
  .
rewrite Rmult_1_r;
 replace
  (-
   (-2 * (yt evader * (sind (heading intruder) * intruderSpeed)) +
    2 * (yt intruder * (sind (heading intruder) * intruderSpeed)) -
    2 * (cosd (heading intruder) * (xt evader * intruderSpeed)) +
    2 * (cosd (heading intruder) * (xt intruder * intruderSpeed)) +
    2 * (xt evader * evaderSpeed) - 2 * (xt intruder * evaderSpeed)))%R with
  ((yt evader * (sind (heading intruder) * intruderSpeed) -
    yt intruder * (sind (heading intruder) * intruderSpeed) +
    cosd (heading intruder) * (xt evader * intruderSpeed) -
    cosd (heading intruder) * (xt intruder * intruderSpeed) -
    xt evader * evaderSpeed + xt intruder * evaderSpeed) * 2)%R.
repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
rewrite Rmult_1_r; ring.
discrR.
ring.
unfold div_tau in H; unfold dxdt, dydt in H; assumption.
assumption.
assumption.
cut
 ((intruderSpeed * cosd (heading intruder) - evaderSpeed)%R =
  (- evaderSpeed + cosd (heading intruder) * intruderSpeed)%R).
cut
 ((intruderSpeed * sind (heading intruder))%R =
  (sind (heading intruder) * intruderSpeed)%R).
intros; rewrite H0; rewrite H1; rewrite Rplus_comm; reflexivity.
ring.
ring.
discrR.
cut
 ((intruderSpeed * cosd (heading intruder) - evaderSpeed)%R =
  (- evaderSpeed + cosd (heading intruder) * intruderSpeed)%R).
cut
 ((intruderSpeed * sind (heading intruder))%R =
  (sind (heading intruder) * intruderSpeed)%R).
intros; rewrite <- H0; rewrite <- H1; rewrite Rplus_comm; assumption.
ring.
ring.
Qed.

(**********)
Lemma Ax2_R_0_div_tau :
 forall intruder evader : State,
 div_tau intruder evader = 0%R -> Ax2_R intruder = 0%R.
unfold div_tau, Ax2_R in |- *; intros; unfold dxdt, dydt in H;
 rewrite Rplus_comm;
 replace (- evaderSpeed + cosd (heading intruder) * intruderSpeed)%R with
  (intruderSpeed * cosd (heading intruder) - evaderSpeed)%R;
 [ rewrite (Rmult_comm (sind (heading intruder))); assumption | ring ].
Qed.

(**********)
Lemma div_tau_0_Ax2_R :
 forall intruder evader : State,
 Ax2_R intruder = 0%R -> div_tau intruder evader = 0%R.
unfold div_tau, Ax2_R in |- *; intros; unfold dxdt, dydt in |- *;
 replace (intruderSpeed * cosd (heading intruder) - evaderSpeed)%R with
  (- evaderSpeed + cosd (heading intruder) * intruderSpeed)%R;
 [ rewrite <- (Rmult_comm (sind (heading intruder))); rewrite Rplus_comm;
    assumption
 | ring ].
Qed.

(**********)
Lemma R_Rmin :
 forall (intruder evader : State) (t : R),
 div_tau intruder evader <> 0%R ->
 Rsqr (RR intruder evader t) =
 (Ax2_R intruder * Rsqr (t - tmin intruder evader) +
  Rsqr_Rmin intruder evader)%R.
Proof with trivial.
intros; unfold Rsqr_Rmin in |- *; case (Req_EM_var (Ax2_R intruder) 0); intro...
elim H; apply div_tau_0_Ax2_R...
rewrite Rsqr_minus; rewrite (tmin_0 intruder evader H); rewrite Rsqr_div...
unfold Rdiv in |- *; rewrite Rsqr_R; rewrite <- Rsqr_neg; rewrite Rsqr_mult;
 replace (Rsqr 2) with 4%R...
rewrite (Rinv_mult_distr 2 (Ax2_R intruder))...
rewrite (Rinv_mult_distr 4 (Ax2_R intruder))...
rewrite Rinv_mult_distr...
unfold Rminus in |- *; do 2 rewrite Rmult_plus_distr_l...
rewrite <-
 (Rmult_comm (Rsqr (Bx_R intruder evader) * (/ 4 * / Rsqr (Ax2_R intruder))))
 ; unfold Rsqr in |- *;
 rewrite (Rinv_mult_distr (Ax2_R intruder) (Ax2_R intruder))...
repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
rewrite Rmult_1_r...
repeat rewrite Rplus_assoc; apply Rplus_eq_compat_l...
rewrite
 (Rmult_plus_distr_r (4 * (Ax2_R intruder * C_R intruder evader))
    (- (Bx_R intruder evader * Bx_R intruder evader))
    (/ 4 * / Ax2_R intruder))...
replace
 (Ax2_R intruder *
  - (2 * (t * (- Bx_R intruder evader * (/ 2 * / Ax2_R intruder)))))%R with
 (Bx_R intruder evader * t)%R...
replace
 (4 * (Ax2_R intruder * C_R intruder evader) * (/ 4 * / Ax2_R intruder))%R
 with (C_R intruder evader)...
ring...
rewrite (Rmult_comm (/ 4))...
repeat rewrite Rmult_assoc...
rewrite (Rmult_comm 4)...
repeat rewrite Rmult_assoc...
rewrite <- Rinv_l_sym...
rewrite Rmult_1_r; rewrite (Rmult_comm (C_R intruder evader));
 repeat rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym...
symmetry  in |- *; apply Rmult_1_l...
discrR...
rewrite (Rmult_comm (Ax2_R intruder));
 replace
  (- (2 * (t * (- Bx_R intruder evader * (/ 2 * / Ax2_R intruder)))))%R with
  (-2 * t * - Bx_R intruder evader * / 2 * / Ax2_R intruder)%R...
repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym...
rewrite Rmult_1_r; repeat rewrite <- Rmult_assoc;
 replace (-2 * t * - Bx_R intruder evader)%R with
  (t * Bx_R intruder evader * 2)%R...
repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym...
ring...
discrR...
ring...
ring...
discrR...
unfold Rsqr in |- *; apply prod_neq_R0...
discrR...
discrR...
apply prod_neq_R0...
Qed.

(**********)
Lemma dx_dxdt :
 forall (intruder evader : State) (t : R),
 (xt intruder - xt evader + t * dxdt intruder)%R = dx intruder evader t.
intros; unfold dxdt, dx in |- *; ring.
Qed.

Lemma dy_dydt :
 forall (intruder evader : State) (t : R),
 (yt intruder - yt evader + t * dydt intruder)%R = dy intruder evader t.
intros; unfold dydt, dy in |- *; ring.
Qed.

(**********)
Lemma R_equal_when_zero :
 forall (intruder evader : State) (t1 t2 : R),
 div_tau intruder evader = 0%R ->
 RR intruder evader t1 = RR intruder evader t2.
intros; unfold RR in |- *; unfold div_tau in H;
 generalize
  (Rplus_eq_R0 (Rsqr (dxdt intruder)) (Rsqr (dydt intruder))
     (Rle_0_sqr (dxdt intruder)) (Rle_0_sqr (dydt intruder)) H); 
 intro; elim H0; intros; generalize (Rsqr_eq_0 (dxdt intruder) H1); 
 intro; generalize (Rsqr_eq_0 (dydt intruder) H2); 
 intro; rewrite <- (dx_dxdt intruder evader t1);
 rewrite <- (dx_dxdt intruder evader t2);
 rewrite <- (dy_dydt intruder evader t1);
 rewrite <- (dy_dydt intruder evader t2); rewrite H3; 
 rewrite H4; repeat rewrite Rmult_0_r; repeat rewrite Rplus_0_r; 
 reflexivity.
Qed.

(**********)
Lemma RR_pos :
 forall (intruder evader : State) (t : R), (0 <= RR intruder evader t)%R.
intros; unfold RR in |- *; apply sqrt_positivity; apply Rplus_le_le_0_compat;
 apply Rle_0_sqr.
Qed.

(**********)
Lemma derivative_eq_zero_tmin :
 forall (intruder evader : State) (t : R),
 (RR intruder evader (tmin intruder evader) <= RR intruder evader t)%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro.
right; apply (R_equal_when_zero intruder evader (tmin intruder evader) t e).
apply Rsqr_incr_0.
repeat rewrite R_Rmin.
apply Rplus_le_compat_r; apply Rmult_le_compat_l.
apply Ax2_R_pos.
unfold Rminus in |- *; rewrite Rplus_opp_r; rewrite Rsqr_0; apply Rle_0_sqr.
assumption.
assumption.
apply RR_pos.
apply RR_pos.
Qed.

(**********)
Lemma derivative_eq_zero_min :
 forall (intruder evader : State) (t1 t2 : R),
 (RR intruder evader (t1 + tau intruder evader t1) <=
  RR intruder evader (t1 + t2))%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro;
 [ right; apply R_equal_when_zero; assumption
 | rewrite (tau_tmin intruder evader t1 n);
    replace (t1 + (tmin intruder evader - t1))%R with (tmin intruder evader);
    [ apply derivative_eq_zero_tmin | ring ] ].
Qed.

(**********)
Lemma asymptotic_decrease_tmin :
 forall (intruder evader : State) (t1 t2 : R),
 (t2 <= tmin intruder evader)%R ->
 (t1 <= t2)%R -> (RR intruder evader t2 <= RR intruder evader t1)%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro.
right; apply (R_equal_when_zero intruder evader t2 t1 e).
apply Rsqr_incr_0.
repeat rewrite R_Rmin.
apply Rplus_le_compat_r; apply Rmult_le_compat_l.
apply Ax2_R_pos.
case (Rtotal_order (tmin intruder evader) t1); intro.
generalize (Rle_lt_trans t2 (tmin intruder evader) t1 H H1); intro;
 elim (Rlt_irrefl t1 (Rle_lt_trans t1 t2 t1 H0 H2)).
elim H1; intros.
rewrite H2 in H; generalize (Rle_antisym t1 t2 H0 H); intro; rewrite H3;
 right; reflexivity.
rewrite Rsqr_neg; rewrite (Rsqr_neg (t1 - tmin intruder evader));
 replace (- (t2 - tmin intruder evader))%R with (tmin intruder evader - t2)%R.
replace (- (t1 - tmin intruder evader))%R with (tmin intruder evader - t1)%R.
apply Rsqr_incr_1.
unfold Rminus in |- *; apply Rplus_le_compat_l; apply Ropp_ge_le_contravar;
 apply Rle_ge; assumption.
apply Rplus_le_reg_l with t2; rewrite Rplus_0_r; rewrite Rplus_comm;
 unfold Rminus in |- *; repeat rewrite Rplus_assoc; 
 rewrite Rplus_opp_l; rewrite Rplus_0_r; assumption.
apply Rplus_le_reg_l with t1; rewrite Rplus_0_r; rewrite Rplus_comm;
 unfold Rminus in |- *; repeat rewrite Rplus_assoc; 
 rewrite Rplus_opp_l; rewrite Rplus_0_r; apply Rle_trans with t2; 
 assumption.
ring.
ring.
assumption.
assumption.
apply RR_pos.
apply RR_pos.
Qed.

Lemma asymptotic_decrease_tau :
 forall (intruder evader : State) (t t1 t2 : R),
 (t2 <= tau intruder evader t)%R ->
 (t1 <= t2)%R ->
 (RR intruder evader (t + t2) <= RR intruder evader (t + t1))%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro;
 [ right; apply R_equal_when_zero; assumption
 | rewrite (tau_tmin intruder evader t n) in H;
    apply asymptotic_decrease_tmin;
    [ apply Rplus_le_reg_l with (- t)%R; repeat rewrite <- Rplus_assoc;
       rewrite Rplus_opp_l; rewrite Rplus_0_l; rewrite Rplus_comm; 
       assumption
    | apply (Rplus_le_compat_l t t1 t2 H0) ] ].
Qed.

Lemma asymptotic_increase_tmin :
 forall (intruder evader : State) (t1 t2 : R),
 (tmin intruder evader <= t1)%R ->
 (t1 <= t2)%R -> (RR intruder evader t1 <= RR intruder evader t2)%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro.
right; apply (R_equal_when_zero intruder evader t1 t2 e).
apply Rsqr_incr_0.
repeat rewrite R_Rmin.
apply Rplus_le_compat_r; apply Rmult_le_compat_l.
apply Ax2_R_pos.
apply Rsqr_incr_1.
unfold Rminus in |- *; apply Rplus_le_compat_r; assumption.
apply Rplus_le_reg_l with (tmin intruder evader); rewrite Rplus_0_r;
 rewrite Rplus_comm; unfold Rminus in |- *; repeat rewrite Rplus_assoc;
 rewrite Rplus_opp_l; rewrite Rplus_0_r; assumption.
apply Rplus_le_reg_l with (tmin intruder evader); rewrite Rplus_0_r;
 rewrite Rplus_comm; unfold Rminus in |- *; repeat rewrite Rplus_assoc;
 rewrite Rplus_opp_l; rewrite Rplus_0_r; apply Rle_trans with t1; 
 assumption.
assumption.
assumption.
apply RR_pos.
apply RR_pos.
Qed.

Lemma asymptotic_increase_tau :
 forall (intruder evader : State) (t t1 t2 : R),
 (tau intruder evader t <= t1)%R ->
 (t1 <= t2)%R ->
 (RR intruder evader (t + t1) <= RR intruder evader (t + t2))%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro;
 [ right; apply R_equal_when_zero; assumption
 | rewrite (tau_tmin intruder evader t n) in H;
    apply asymptotic_increase_tmin;
    [ apply Rplus_le_reg_l with (- t)%R; repeat rewrite <- Rplus_assoc;
       rewrite Rplus_opp_l; rewrite Rplus_0_l; rewrite Rplus_comm; 
       assumption
    | apply (Rplus_le_compat_l t t1 t2 H0) ] ].
Qed.

(**********)
Lemma tau_equal_when_zero :
 forall (intruder evader : State) (t : R),
 div_tau intruder evader = 0%R -> tau intruder evader t = 0%R.
intros; unfold tau in |- *; case (Req_EM_var (div_tau intruder evader) 0);
 intro; [ reflexivity | elim n; exact H ].
Qed.

Lemma asymptotic_tau_gt :
 forall (intruder evader : State) (t dt : R),
 (0 <= dt)%R ->
 (RR intruder evader (t + dt) < RR intruder evader t)%R ->
 (0 < tau intruder evader t)%R.
intros; case (Rtotal_order 0 (tau intruder evader t)); intro;
 [ assumption
 | cut (tau intruder evader t <= 0)%R;
    [ intro; elim H1; intro;
       generalize (asymptotic_increase_tau intruder evader t 0 dt H2 H);
       rewrite Rplus_0_r; intro;
       elim
        (Rlt_irrefl (RR intruder evader t)
           (Rle_lt_trans (RR intruder evader t) (RR intruder evader (t + dt))
              (RR intruder evader t) H4 H0))
    | elim H1; intro;
       [ right; symmetry  in |- *; assumption | left; assumption ] ] ].
Qed.

(**********)
Lemma tau_is_uniform :
 forall (intruder evader : State) (t1 t2 : R),
 div_tau intruder evader <> 0%R ->
 tau intruder evader (t1 + t2) = (tau intruder evader t1 - t2)%R.
intros; case (Req_EM_var (div_tau intruder evader) 0); intro;
 [ elim H; exact e | repeat rewrite tau_tmin; [ ring | exact H | exact H ] ].
Qed.

(**********)
Lemma tau_gt_time :
 forall (intruder evader : State) (t1 t2 t : R),
 (t < tau intruder evader t2)%R ->
 (t1 <= t2)%R -> (t < tau intruder evader t1)%R.
intros.
case (Req_EM_var (div_tau intruder evader) 0); intro.
rewrite (tau_equal_when_zero intruder evader t1 e).
rewrite (tau_equal_when_zero intruder evader t2 e) in H.
assumption.
cut (t1 = (t2 + (t1 - t2))%R).
intro.
rewrite H1.
rewrite (tau_is_uniform intruder evader t2 (t1 - t2) n).
unfold Rminus in |- *.
cut (0 <= - (t1 - t2))%R.
intro.
generalize
 (Rplus_lt_le_compat t (tau intruder evader t2) 0 (- (t1 - t2)) H H2).
rewrite Rplus_0_r.
intro; assumption.
rewrite <- Ropp_0.
apply Ropp_ge_le_contravar.
apply Rle_ge.
apply Rplus_le_reg_l with t2.
rewrite <- H1; rewrite Rplus_0_r; assumption.
ring.
Qed.

Lemma tau_ge_time :
 forall (intruder evader : State) (t1 t2 t : R),
 (t <= tau intruder evader t2)%R ->
 (t1 <= t2)%R -> (t <= tau intruder evader t1)%R.
intros.
case (Req_EM_var (div_tau intruder evader) 0); intro.
rewrite (tau_equal_when_zero intruder evader t1 e).
rewrite (tau_equal_when_zero intruder evader t2 e) in H.
assumption.
cut (t1 = (t2 + (t1 - t2))%R).
intro.
rewrite H1.
rewrite (tau_is_uniform intruder evader t2 (t1 - t2) n).
unfold Rminus in |- *.
cut (0 <= - (t1 - t2))%R.
intro.
generalize (Rplus_le_compat t (tau intruder evader t2) 0 (- (t1 - t2)) H H2).
rewrite Rplus_0_r.
intro; assumption.
rewrite <- Ropp_0.
apply Ropp_ge_le_contravar.
apply Rle_ge.
apply Rplus_le_reg_l with t2.
rewrite <- H1; rewrite Rplus_0_r; assumption.
ring.
Qed.
