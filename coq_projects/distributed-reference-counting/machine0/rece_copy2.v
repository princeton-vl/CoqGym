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


(* RECEIVE COPY 2 *)

(*definit la deuxieme transition receive copy et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_REC_COP2.

Definition rec_copy2_trans (c : Config) (s2 : Site) :=
  mkconfig (S (time c)) (dt c) (st c) (Set_rec_table (rt c) s2)
    (Collect_message (bm c) owner s2).

End DEF_REC_COP2.

Section REC_COP2_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s2 : Site.

Hypothesis rt_true : rt c0 s2 = false.

Lemma rcop2_trans_le_dt_time :
 forall s0 : Site,
 dt c0 s0 <= time c0 ->
 dt (rec_copy2_trans c0 s2) s0 <= time (rec_copy2_trans c0 s2).
Proof.
 simpl in |- *; auto.
Qed.

Lemma rcop2_trans_diff_site :
 forall s3 s4 : Site,
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (rec_copy2_trans c0 s2) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; apply H.
 apply in_collect with (s1 := owner) (s2 := s2); trivial.
Qed.

Lemma rcop2_trans_rt :
 forall s0 : Site,
 Int (rt (rec_copy2_trans c0 s2) s0) =
 (if eq_site_dec s0 s2
  then  (Int (rt c0 s0) + 1)%Z
  else  Int (rt c0 s0)).
Proof.
 intro; case (eq_site_dec s0 s2); simpl in |- *; intros.
 rewrite e; apply S_set_rec_table; auto.
 apply no_set_rec_table; auto.
Qed.

Lemma rcop2_trans_in_queue :
 forall s0 s3 s4 : Site,
 In_queue Message (inc_dec s0) (bm (rec_copy2_trans c0 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 simpl in |- *; intros.
 apply in_collect with (s1 := owner) (s2 := s2); auto.
Qed.

Lemma rcop2_trans_st_rt :
 forall s0 : Site,
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (rec_copy2_trans c0 s2) s0 > 0)%Z ->
 rt (rec_copy2_trans c0 s2) s0 = true.
Proof.
 simpl in |- *; intros; auto; case (eq_site_dec s0 s2); intro.
 rewrite e; apply true_set_rec_table.

 rewrite inch_set_rec_table; auto.
Qed.

End REC_COP2_EFFECT.

Section REC_COP2_CTRL.

(* decompte de messages *)

Variable c0 : Config.

Variable s0 s2 : Site.

Hypothesis first_mess : first Message (bm c0 owner s2) = value Message copy.

Lemma rcop2_trans_ctrl_copy :
 forall s1 : Site,
 ctrl_copy s0 s1 (bm (rec_copy2_trans c0 s2)) =
 (if eq_site_dec s0 owner
  then
   
   if eq_site_dec s1 s2
   then  (ctrl_copy s0 s1 (bm c0) - 1)%Z
   else  ctrl_copy s0 s1 (bm c0)
  else  ctrl_copy s0 s1 (bm c0)).
Proof.
 intros; unfold ctrl_copy in |- *; simpl in |- *.
 case (eq_site_dec s0 owner); intro.
 case (eq_site_dec s1 s2); intro.
 rewrite e; rewrite e0; apply collect_card_mess; trivial.

 apply diff_collect_card_mess; auto.

 apply diff_collect_card_mess; auto.
Qed.

Lemma rcop2_trans_ctrl_dec :
 forall s1 : Site,
 ctrl_dec s0 s1 (bm (rec_copy2_trans c0 s2)) = ctrl_dec s0 s1 (bm c0).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].
Qed.

Lemma rcop2_trans_ctrl_inc :
 forall s1 : Site,
 ctrl_inc s0 s1 (bm (rec_copy2_trans c0 s2)) = ctrl_inc s0 s1 (bm c0).
Proof.
 intros; unfold ctrl_inc in |- *; simpl in |- *.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].
Qed.

Remark rcop2_trans_sigma_copy :
 s0 <> owner ->
 sigma_ctrl_copy s0 (bm (rec_copy2_trans c0 s2)) = sigma_ctrl_copy s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 apply sigma_simpl; intros.
 rewrite rcop2_trans_ctrl_copy.
 apply case_ineq; trivial.
Qed.

Remark rcop2_trans_sigma_dec :
 sigma_ctrl_dec s0 (bm (rec_copy2_trans c0 s2)) = sigma_ctrl_dec s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 apply sigma_simpl; intros; apply rcop2_trans_ctrl_dec.
Qed.

Remark rcop2_trans_sigma_inc :
 sigma_ctrl_inc s0 (bm (rec_copy2_trans c0 s2)) = sigma_ctrl_inc s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 apply sigma_simpl; intros; apply rcop2_trans_ctrl_inc.
Qed.

Lemma rcop2_trans_sigma_ctrl :
 s0 <> owner ->
 sigma_ctrl s0 (bm (rec_copy2_trans c0 s2)) = sigma_ctrl s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite rcop2_trans_sigma_copy.
 rewrite rcop2_trans_sigma_dec.
 rewrite rcop2_trans_sigma_inc.
 trivial.

 trivial.
Qed.

End REC_COP2_CTRL.

Section REC_COP2_XY.

Variable c0 : Config.

Variable s0 s2 : Site.

Hypothesis rt_true : rt c0 s2 = false.

Hypothesis first_mess : first Message (bm c0 owner s2) = value Message copy.

Remark rcop2_trans_xi :
 forall s1 : Site, xi (rec_copy2_trans c0 s2) s1 = xi c0 s1.
Proof.
 intro; unfold xi in |- *.
 rewrite rcop2_trans_ctrl_copy.
 rewrite rcop2_trans_ctrl_dec.
 rewrite rcop2_trans_rt.
 rewrite case_eq; case (eq_site_dec s1 s2); intro.
 omega.

 trivial.

 trivial.

 trivial.

 trivial.
Qed.

Remark rcop2_trans_yi :
 forall s1 : Site, yi (rec_copy2_trans c0 s2) s1 = yi c0 s1.
Proof.
 intro; unfold yi in |- *; apply sigma_simpl.
 intros; apply rcop2_trans_ctrl_inc; trivial.
Qed.

Lemma rcop2_trans_sigma_xi : sigma_xi (rec_copy2_trans c0 s2) = sigma_xi c0.
Proof.
 unfold sigma_xi in |- *; apply sigma_simpl; intros; apply rcop2_trans_xi.
Qed.

Lemma rcop2_trans_sigma_yi : sigma_yi (rec_copy2_trans c0 s2) = sigma_yi c0.
Proof.
 unfold sigma_yi in |- *; apply sigma_simpl; intros; apply rcop2_trans_yi.
Qed.

End REC_COP2_XY.

Section REC_COP2_ALT.

(* structure de file d'attente *)

Variable c0 : Config.

Variable s0 s2 : Site.

Lemma rcop2_trans_D :
 (rt c0 s0 = false -> D_queue (bm c0 s0 owner)) ->
 rt (rec_copy2_trans c0 s2) s0 = false ->
 D_queue (bm (rec_copy2_trans c0 s2) s0 owner).
Proof.
 simpl in |- *; case (eq_site_dec s2 s0); intro.
 rewrite e; rewrite true_set_rec_table; intros; discriminate H0.

 rewrite inch_set_rec_table.
 intros; apply D_collect; auto.

 trivial.
Qed.

Lemma rcop2_trans_alt :
 alternate (bm c0 s0 owner) ->
 alternate (bm (rec_copy2_trans c0 s2) s0 owner).
Proof.
 intros; simpl in |- *; apply alt_collect; trivial.
Qed.

End REC_COP2_ALT.

Section REC_COP2_RELAT.

(* relation parent *)

Variable c0 : Config.

Variable s2 : Site.

Remark rcop2_trans_parent :
 forall s3 s4 : Site, parent (rec_copy2_trans c0 s2) s4 s3 -> parent c0 s4 s3.
Proof.
 intros; elim H.
 intros; apply parent_intro.
 apply rcop2_trans_in_queue with (s2 := s2); trivial.
Qed.

Lemma rcop2_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (rec_copy2_trans c0 s2) s3 s4 ->
 dt (rec_copy2_trans c0 s2) s3 < dt (rec_copy2_trans c0 s2) s4.
Proof.
 simpl in |- *; intros; apply H.
 apply rcop2_trans_parent; trivial.
Qed.

End REC_COP2_RELAT.
