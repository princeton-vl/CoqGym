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


(* DELETE *)

(*definit la transition delete et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_DEL.

Definition delete_trans (c : Config) (s : Site) :=
  mkconfig (S (time c)) (dt c) (st c) (Reset_rec_table (rt c) s)
    (Post_message dec (bm c) s owner).

End DEF_DEL.

Section DEL_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s0 : Site.

Hypothesis rt_true : rt c0 s0 = true.

Lemma del_trans_le_dt_time :
 forall s1 : Site,
 dt c0 s1 <= time c0 ->
 dt (delete_trans c0 s0) s1 <= time (delete_trans c0 s0).
Proof.
 simpl in |- *; auto.
Qed.

Lemma del_trans_diff_site :
 forall s3 s4 : Site,
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (delete_trans c0 s0) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; apply H. 
 apply in_post with (m' := dec) (s1 := s0) (s2 := owner).
 discriminate.

 trivial.
Qed.

Lemma del_trans_rt :
 forall s1 : Site,
 Int (rt (delete_trans c0 s0) s1) =
 (if eq_site_dec s1 s0
  then  (Int (rt c0 s1) - 1)%Z
  else  Int (rt c0 s1)).
Proof.
 intro; case (eq_site_dec s1 s0); simpl in |- *; intros.
 rewrite e; apply pred_reset_rec_table; auto.
 apply no_reset_rec_table; auto.
Qed.

Lemma del_trans_in_queue :
 forall s1 s3 s4 : Site,
 In_queue Message (inc_dec s0) (bm (delete_trans c0 s1) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 intros; apply in_post with (m' := dec) (s1 := s1) (s2 := owner).
 discriminate.

 auto.
Qed.

Lemma del_trans_st_rt :
 forall s1 : Site,
 st c0 s1 = 0%Z ->
 rt c0 s1 = true ->
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (delete_trans c0 s1) s0 > 0)%Z -> rt (delete_trans c0 s1) s0 = true.
Proof.
 simpl in |- *; intros; auto.
 case (eq_site_dec s0 s1); intro.
 rewrite e in H2; absurd (st c0 s1 = 0%Z); omega.

 rewrite inch_reset_rec_table; auto.
Qed.

End DEL_EFFECT.

Section DEL_CTRL.

(* decompte de messages *)

Variable c0 : Config.

Variable s0 s1 : Site.

Lemma del_trans_ctrl_copy :
 forall s2 : Site,
 ctrl_copy s0 s2 (bm (delete_trans c0 s1)) = ctrl_copy s0 s2 (bm c0).
Proof.
 intros; unfold ctrl_copy in |- *; simpl in |- *.
 apply diff_post_card_mess.
 left; discriminate.
Qed.

Lemma del_trans_ctrl_dec :
 forall s2 : Site,
 ctrl_dec s0 s2 (bm (delete_trans c0 s1)) =
 (if eq_site_dec owner s0
  then
   
   if eq_site_dec s2 s1
   then  (ctrl_dec s0 s2 (bm c0) + 1)%Z
   else  ctrl_dec s0 s2 (bm c0)
  else  ctrl_dec s0 s2 (bm c0)).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 case (eq_site_dec owner s0); intro.
 case (eq_site_dec s2 s1); intro.
 rewrite e; rewrite e0; apply post_card_mess.

 apply diff_post_card_mess; auto.

 apply diff_post_card_mess; auto.
Qed.

Lemma del_trans_ctrl_inc :
 forall s2 : Site,
 ctrl_inc s0 s2 (bm (delete_trans c0 s1)) = ctrl_inc s0 s2 (bm c0).
Proof.
 intros; unfold ctrl_inc in |- *; simpl in |- *.
 apply diff_post_card_mess.
 left; discriminate.
Qed.

Remark del_trans_sigma_copy :
 sigma_ctrl_copy s0 (bm (delete_trans c0 s1)) = sigma_ctrl_copy s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 apply sigma_simpl; intros; apply del_trans_ctrl_copy.
Qed.

Remark del_trans_sigma_dec :
 s0 <> owner ->
 sigma_ctrl_dec s0 (bm (delete_trans c0 s1)) = sigma_ctrl_dec s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 apply sigma_simpl; intros. 
 rewrite del_trans_ctrl_dec; apply case_ineq; auto.
Qed.

Remark del_trans_sigma_inc :
 sigma_ctrl_inc s0 (bm (delete_trans c0 s1)) = sigma_ctrl_inc s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 apply sigma_simpl; intros; apply del_trans_ctrl_inc.
Qed.

Lemma del_trans_sigma_ctrl :
 s0 <> owner ->
 sigma_ctrl s0 (bm (delete_trans c0 s1)) = sigma_ctrl s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite del_trans_sigma_copy.
 rewrite del_trans_sigma_dec.
 rewrite del_trans_sigma_inc.
 trivial.

 trivial.
Qed.

End DEL_CTRL.

Section DEL_XY.

Variable c0 : Config.

Variable s1 : Site.

Hypothesis rt_true : rt c0 s1 = true.

Remark del_trans_xi : forall s0 : Site, xi (delete_trans c0 s1) s0 = xi c0 s0.
Proof.
 intro; unfold xi in |- *.
 rewrite del_trans_ctrl_copy.
 rewrite del_trans_rt.
 rewrite del_trans_ctrl_dec; rewrite case_eq.
 simpl in |- *; case (eq_site_dec s0 s1); intro.
 omega.

 trivial.

 trivial.
Qed.

Remark del_trans_yi : forall s0 : Site, yi (delete_trans c0 s1) s0 = yi c0 s0.
Proof.
 intro; unfold yi in |- *; apply sigma_simpl.
 intros; apply del_trans_ctrl_inc.
Qed.

Lemma del_trans_sigma_xi : sigma_xi (delete_trans c0 s1) = sigma_xi c0.
Proof.
 unfold sigma_xi in |- *; apply sigma_simpl; intros; apply del_trans_xi.
Qed.

Lemma del_trans_sigma_yi : sigma_yi (delete_trans c0 s1) = sigma_yi c0.
Proof.
 unfold sigma_yi in |- *; apply sigma_simpl; intros; apply del_trans_yi.
Qed.

End DEL_XY.

Section DEL_ALT.

(* structure de file d'attente *)

Variable c0 : Config.

Variable s0 s1 : Site.

Lemma del_trans_D :
 (rt c0 s0 = false -> D_queue (bm c0 s0 owner)) ->
 rt (delete_trans c0 s1) s0 = false ->
 D_queue (bm (delete_trans c0 s1) s0 owner).
Proof.
 case (eq_site_dec s0 s1); simpl in |- *; intro.
 rewrite e; intros; apply D_post_dec.

 rewrite inch_reset_rec_table.
 intros; apply D_post_elsewhere; auto.

 auto.
Qed.

Lemma del_trans_alt :
 alternate (bm c0 s0 owner) -> alternate (bm (delete_trans c0 s1) s0 owner).
Proof.
 case (eq_site_dec s1 s0); intros; simpl in |- *.
 rewrite e; apply alt_post_dec; trivial.

 apply alt_post_elsewhere; auto.
Qed.

End DEL_ALT.

Section DEL_RELAT.

(* relation parent *)

Variable c0 : Config.

Variable s0 : Site.

Remark del_trans_parent :
 forall s1 s2 : Site, parent (delete_trans c0 s0) s2 s1 -> parent c0 s2 s1.
Proof.
 intros; elim H.
 intros; apply parent_intro.
 apply del_trans_in_queue with (s1 := s0); trivial.
Qed.

Lemma del_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (delete_trans c0 s0) s3 s4 ->
 dt (delete_trans c0 s0) s3 < dt (delete_trans c0 s0) s4.
Proof.
 simpl in |- *; intros; apply H.
 apply del_trans_parent; trivial.
Qed.

End DEL_RELAT.
