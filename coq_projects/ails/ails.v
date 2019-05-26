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
Require Import constants.
Require Import ails_def.
Require Import tau.
Require Import Omega.

Unset Standard Proposition Elimination Names.

Fixpoint rest (p r s n : nat) {struct n} : nat :=
  match n with
  | O => r
  | S n' =>
      match s with
      | O => 0
      | S O => rest p 0 p n'
      | S s' => rest p (S r) s' n'
      end
  end.
  
Definition mod_ (m n : nat) : nat := rest n 0 n m.

Lemma mod_eq_0 : forall m : nat, mod_ 0 m = 0.
Proof with trivial.
intro m; unfold mod_ in |- *; unfold rest in |- *...
Qed.

Definition trkrate (phi : Bank) : R :=
  toDeg (g * (tand phi / v intruderSpeed)).

Lemma cond1_0 : (- toDeg MaxBank <= 0)%R.
left; rewrite <- Ropp_0; apply Ropp_lt_gt_contravar; unfold toDeg in |- *;
repeat simple apply Rmult_lt_0_compat.
unfold MaxBank in |- *; unfold Rdiv in |- *; apply Rmult_lt_0_compat.
prove_sup.
apply Rinv_0_lt_compat; prove_sup.
unfold plat in |- *; prove_sup.
apply Rinv_0_lt_compat; apply PI_RGT_0.
Qed.

Lemma cond2_0 : (0 <= toDeg MaxBank)%R.
left; unfold toDeg in |- *; repeat simple apply Rmult_lt_0_compat.
unfold MaxBank in |- *; unfold Rdiv in |- *; apply Rmult_lt_0_compat.
prove_sup.
apply Rinv_0_lt_compat; prove_sup.
unfold plat in |- *; prove_sup.
apply Rinv_0_lt_compat; apply PI_RGT_0.
Qed.

Lemma trkrate0 : trkrate (mkBank 0 cond1_0 cond2_0) = 0%R.
Proof with trivial.
unfold trkrate in |- *; replace (r (mkBank 0 cond1_0 cond2_0)) with 0%R...
unfold toDeg, tand in |- *; unfold toRad in |- *; repeat rewrite Rmult_0_l;
 rewrite tan_0; unfold Rdiv in |- *; repeat rewrite Rmult_assoc;
 repeat rewrite Rmult_0_l; apply Rmult_0_r...
Qed.

Definition distance (s1 s2 : State) : R :=
  sqrt (Rsqr (xt s2 - xt s1) + Rsqr (yt s2 - yt s1)).

Lemma distance_sym : forall s1 s2 : State, distance s1 s2 = distance s2 s1.
Proof with trivial.
intros; unfold distance in |- *; rewrite (Rsqr_neg (xt s2 - xt s1));
 rewrite (Rsqr_neg (yt s2 - yt s1)); repeat rewrite Ropp_minus_distr...
Qed.

Definition alerting_distance (s1 s2 : State) : Prop :=
  (distance s1 s2 <= AlertRange)%R.

Definition conflict_distance (s1 s2 : State) : Prop :=
  (distance s1 s2 <= ConflictRange)%R.

Definition chkrange (range tpred : R) : Prop :=
  (range <= AlertRange)%R /\ (tpred <= AlertTime)%R.

Definition chktrack (intruder evader : State) (tpred : R) : Prop :=
  let tau := tau intruder evader 0 in
  match Rle_dec tau 0 with
  | left _ => chkrange (RR intruder evader 0) tpred
  | right _ =>
      match Rlt_dec AlertTime (tpred + tau) with
      | left _ => (RR intruder evader AlertTime <= AlertRange)%R
      | right _ => (RR intruder evader tau <= AlertRange)%R
      end
  end.

Definition arc_loop (intruder evader : State) (arcrad trkrate : R)
  (idtrk iarc : nat) : Prop :=
  match iarc with
  | S p => False
  | O =>
      let tpred := (INR iarc * tstep)%R in
      let xloc := (xt evader + v evaderSpeed * tpred)%R in
      let yloc := yt evader in
      let xtrk :=
        match Rlt_le_dec 0 trkrate with
        | left _ =>
            (xt intruder +
             arcrad *
             (sind (heading intruder + trkrate * tpred) -
              sind (heading intruder)))%R
        | right _ =>
            (xt intruder +
             arcrad *
             (sind (heading intruder) - sind (heading intruder) +
              trkrate * tpred))%R
        end in
      let ytrk :=
        match Rlt_le_dec 0 trkrate with
        | left _ =>
            (yt intruder +
             arcrad *
             (cosd (heading intruder) -
              cosd (heading intruder + trkrate * tpred)))%R
        | right _ =>
            (yt intruder +
             arcrad *
             (cosd (heading intruder + trkrate * tpred) -
              cosd (heading intruder)))%R
        end in
      match mod_ iarc idtrk with
      | O =>
          let tantrk := (heading intruder + tpred * trkrate)%R in
          let int := mkState xtrk ytrk tantrk (bank intruder) in
          let eva := mkState xloc yloc (heading evader) (bank evader) in
          chktrack int eva tpred
      | _ =>
          let range := sqrt (Rsqr (xtrk - xloc) + Rsqr (ytrk - yloc)) in
          chkrange range tpred
      end
  end.

Definition ails_alert (intruder evader : State) : Prop :=
  let phi := bank intruder in
  let trkrate := trkrate phi in
  match Req_EM_var trkrate 0 with
  | left _ => chktrack intruder evader 0
  | right _ =>
      let arcrad := (Rsqr (v intruderSpeed) / (g * tand (r phi)))%R in
      let idtrk :=
        match Rle_dec 3 trkrate with
        | left _ => 1
        | right _ =>
            match Rle_dec (3 / 2) trkrate with
            | left _ => 2
            | right _ =>
                match Rle_dec (3 / 4) trkrate with
                | left _ => 4
                | right _ => 8
                end
            end
        end in
      arc_loop intruder evader arcrad trkrate idtrk 0
  end.

Lemma R_distance :
 forall intruder evader : State,
 RR intruder evader 0 = distance intruder evader.
Proof with trivial.
intros; unfold RR, distance in |- *; unfold dx, dy in |- *;
 repeat rewrite Rmult_0_l; repeat rewrite Rplus_0_r;
 rewrite (Rsqr_neg (xt intruder - xt evader));
 rewrite (Rsqr_neg (yt intruder - yt evader));
 repeat rewrite Ropp_minus_distr...
Qed.

(*********************************************)
(************** MAIN THEOREM *****************)
(*********************************************)

Lemma step1 :
 forall evader intruder : State,
 alerting_distance evader intruder -> chktrack intruder evader 0.
Proof with trivial.
intros; unfold alerting_distance in H; unfold chktrack in |- *;
 case (Rle_dec (tau intruder evader 0) 0); intro...
unfold chkrange in |- *; split...
rewrite R_distance; rewrite distance_sym...
unfold AlertTime in |- *; left; prove_sup...
case (Rlt_dec AlertTime (0 + tau intruder evader 0)); intro...
rewrite Rplus_0_l in r; cut (0 <= AlertTime)%R...
intro;
 assert
  (H1 :=
   asymptotic_decrease_tau intruder evader 0 0 AlertTime
     (Rlt_le AlertTime (tau intruder evader 0) r) H0);
 repeat rewrite Rplus_0_l in H1; rewrite R_distance in H1;
 rewrite distance_sym in H1; apply Rle_trans with (distance evader intruder)...
unfold AlertTime in |- *; left; prove_sup...
assert (H0 := derivative_eq_zero_min intruder evader 0 0);
 repeat rewrite Rplus_0_l in H0; rewrite R_distance in H0;
 rewrite distance_sym in H0; apply Rle_trans with (distance evader intruder)...
Qed.

Lemma step2 :
 forall (evader intruder : State) (x : nat),
 (distance evader intruder <= AlertRange)%R ->
 trkrate (bank intruder) <> 0%R ->
 arc_loop intruder evader (Rsqr intruderSpeed / (g * tand (bank intruder)))
   (trkrate (bank intruder)) x 0.
Proof with trivial.
intros evader intruder x H n; unfold arc_loop in |- *; rewrite mod_eq_0;
 case (Rlt_le_dec 0 (trkrate (bank intruder)))...
cut (INR 0 = 0%R)...
intros; rewrite H0; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r;
 repeat rewrite Rplus_0_r;
 cut
  (mkState
     (xt intruder +
      Rsqr intruderSpeed / (g * tand (bank intruder)) *
      (sind (heading intruder) - sind (heading intruder)))
     (yt intruder +
      Rsqr intruderSpeed / (g * tand (bank intruder)) *
      (cosd (heading intruder) - cosd (heading intruder))) 
     (heading intruder) (bank intruder) = intruder)...
cut (mkState (xt evader) (yt evader) (heading evader) (bank evader) = evader)...
intros; rewrite H1; rewrite H2; unfold chktrack in |- *;
 case (Rle_dec (tau intruder evader 0) 0); intro...
unfold chkrange in |- *; split...
unfold RR in |- *; unfold dx, dy in |- *; repeat rewrite Rmult_0_l;
 repeat rewrite Rplus_0_r; unfold distance in H...
unfold AlertTime in |- *; left; prove_sup...
rewrite Rplus_0_l; case (Rlt_dec AlertTime (tau intruder evader 0)); intro...
cut (0 <= AlertTime)%R...
intro;
 assert
  (H4 :=
   asymptotic_decrease_tau intruder evader 0 0 AlertTime (Rlt_le _ _ r0) H3);
 repeat rewrite Rplus_0_l in H4; apply Rle_trans with (RR intruder evader 0)...
unfold RR in |- *; unfold dx, dy in |- *; repeat rewrite Rmult_0_l;
 repeat rewrite Rplus_0_r...
unfold AlertTime in |- *; left; prove_sup...
assert (H3 := derivative_eq_zero_min intruder evader 0 0);
 repeat rewrite Rplus_0_l in H3; apply Rle_trans with (RR intruder evader 0)...
unfold RR in |- *; unfold dx, dy in |- *; repeat rewrite Rmult_0_l;
 repeat rewrite Rplus_0_r...
unfold xt, yt in |- *; case evader...
unfold xt, yt in |- *; case intruder; intros; unfold Rminus in |- *;
 repeat rewrite Rplus_opp_r; repeat rewrite Rmult_0_r;
 repeat rewrite Rplus_0_r...
cut (INR 0 = 0%R)...
intros; rewrite H0; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r;
 repeat rewrite Rplus_0_r;
 cut
  (mkState
     (xt intruder +
      Rsqr intruderSpeed / (g * tand (bank intruder)) *
      (sind (heading intruder) - sind (heading intruder)))
     (yt intruder +
      Rsqr intruderSpeed / (g * tand (bank intruder)) *
      (cosd (heading intruder) - cosd (heading intruder))) 
     (heading intruder) (bank intruder) = intruder)... cut
  (mkState (xt evader) (yt evader) (heading evader) (bank evader) = evader)...
intros; rewrite H1; rewrite H2; unfold chktrack in |- *;
 case (Rle_dec (tau intruder evader 0) 0); intro...
unfold chkrange in |- *; split...
unfold RR in |- *; unfold dx, dy in |- *; repeat rewrite Rmult_0_l;
 repeat rewrite Rplus_0_r; unfold distance in H...
unfold AlertTime in |- *; left; prove_sup...
rewrite Rplus_0_l; case (Rlt_dec AlertTime (tau intruder evader 0)); intro...
cut (0 <= AlertTime)%R...
intro;
 assert
  (H4 :=
   asymptotic_decrease_tau intruder evader 0 0 AlertTime (Rlt_le _ _ r0) H3);
 repeat rewrite Rplus_0_l in H4; apply Rle_trans with (RR intruder evader 0)...
unfold RR in |- *; unfold dx, dy in |- *; repeat rewrite Rmult_0_l;
 repeat rewrite Rplus_0_r...
unfold AlertTime in |- *; left; prove_sup...
assert (H3 := derivative_eq_zero_min intruder evader 0 0);
 repeat rewrite Rplus_0_l in H3; apply Rle_trans with (RR intruder evader 0)...
unfold RR in |- *; unfold dx, dy in |- *; repeat rewrite Rmult_0_l;
 repeat rewrite Rplus_0_r...
unfold xt, yt in |- *; case evader...
unfold xt, yt in |- *; case intruder; intros; unfold Rminus in |- *;
 repeat rewrite Rplus_opp_r; repeat rewrite Rmult_0_r;
 repeat rewrite Rplus_0_r...
Qed.

Theorem alarm_at_alerting_distance :
 forall evader intruder : State,
 alerting_distance evader intruder -> ails_alert intruder evader.
Proof with trivial.
intros; unfold ails_alert in |- *;
 case (Req_EM_var (trkrate (bank intruder)) 0); intro...
apply (step1 _ _ H)...
unfold alerting_distance in H; case (Rle_dec 3 (trkrate (bank intruder)));
 intro...
apply step2...
case (Rle_dec (3 / 2) (trkrate (bank intruder))); intro...
apply step2...
case (Rle_dec (3 / 4) (trkrate (bank intruder))); intro; apply step2...
Qed.
