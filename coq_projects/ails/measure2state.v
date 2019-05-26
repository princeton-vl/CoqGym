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
Require Import trajectory_def.
Require Import constants.
Require Import ails_def.
Require Import Omega.

Lemma cond1_sty :
 forall (tr : Trajectory) (t : R), (- toDeg MaxBank <= toDeg (phi tr t))%R.
Proof with trivial.
intros; unfold toDeg in |- *; repeat rewrite Rmult_assoc;
 rewrite <- Ropp_mult_distr_l_reverse; rewrite (Rmult_comm (- MaxBank));
 rewrite (Rmult_comm (phi tr t)); apply Rmult_le_compat_l...
left; apply Rmult_lt_0_compat... 
unfold plat in |- *; prove_sup0...
apply Rinv_0_lt_compat; apply PI_RGT_0...
generalize (cond_phi tr); intro H; elim (H t)...
Qed.

Lemma cond2_sty :
 forall (tr : Trajectory) (t : R), (toDeg (phi tr t) <= toDeg MaxBank)%R.
Proof with trivial.
intros; unfold toDeg in |- *; repeat rewrite Rmult_assoc;
 rewrite (Rmult_comm MaxBank); rewrite (Rmult_comm (phi tr t));
 apply Rmult_le_compat_l...
left; apply Rmult_lt_0_compat... 
unfold plat in |- *; prove_sup...
apply Rinv_0_lt_compat; apply PI_RGT_0...
generalize (cond_phi tr); intro H; elim (H t)...
Qed.


Definition measure2state (tr : Trajectory) (t : R) : State :=
  mkState (x tr t) (y tr t) (toDeg (theta tr t))
    (mkBank (toDeg (phi tr t)) (cond1_sty tr t) (cond2_sty tr t)).