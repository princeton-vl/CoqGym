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


(* RECEIVE INC *)

(*definit la transition receive inc et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_REC_INC.

Definition rec_inc_trans (c : Config) (s1 s3 : Site) :=
  mkconfig (S (time c)) (dt c) (Inc_send_table (st c) owner) 
    (rt c) (Post_message dec (Collect_message (bm c) s1 owner) owner s3). 

End DEF_REC_INC.

Section REC_INC_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s1 s2 : Site.

Lemma rinc_trans_le_dt_time :
 forall s0 : Site,
 dt c0 s0 <= time c0 ->
 dt (rec_inc_trans c0 s1 s2) s0 <= time (rec_inc_trans c0 s1 s2).
Proof.
 simpl in |- *; auto.
Qed.

Lemma rinc_trans_diff_site :
 forall s3 s4 : Site,
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (rec_inc_trans c0 s1 s2) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; apply H.
 apply in_collect with (s1 := s1) (s2 := owner).
 apply in_post with (m' := dec) (s1 := owner) (s2 := s2).
 discriminate.

 trivial.
Qed.

Lemma rinc_trans_st :
 forall s0 : Site,
 st (rec_inc_trans c0 s1 s2) s0 =
 (if eq_site_dec s0 owner
  then (st c0 s0 + 1)%Z
  else st c0 s0).
Proof.
 intro; simpl in |- *; case (eq_site_dec s0 owner); intro.
 rewrite e; apply S_inc_send_table.

 apply no_inc_send_table; auto.
Qed.

Lemma rinc_trans_in_queue :
 forall s0 s3 s4 : Site,
 In_queue Message (inc_dec s0) (bm (rec_inc_trans c0 s1 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 simpl in |- *; intros.
 apply in_collect with (s1 := s1) (s2 := owner).
 apply in_post with (m' := dec) (s1 := owner) (s2 := s2).
 discriminate.

 auto.
Qed.

Lemma rinc_trans_st_rt :
 forall s0 : Site,
 s0 <> owner ->
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (rec_inc_trans c0 s1 s2) s0 > 0)%Z ->
 rt (rec_inc_trans c0 s1 s2) s0 = true.
Proof.
 intros s0 H; simpl in |- *.
 rewrite no_inc_send_table; auto.
Qed.

End REC_INC_EFFECT.

Section REC_INC_CTRL.

(* decomptes de messages *)

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis
  first_mess : first Message (bm c0 s1 owner) = value Message (inc_dec s2).

Lemma rinc_trans_ctrl_copy :
 forall s0 s3 : Site,
 ctrl_copy s0 s3 (bm (rec_inc_trans c0 s1 s2)) = ctrl_copy s0 s3 (bm c0).
Proof.
 intros; unfold ctrl_copy in |- *; simpl in |- *.
 rewrite diff_post_card_mess.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := inc_dec s2); [ trivial | discriminate ].

 left; discriminate.
Qed.

Lemma rinc_trans_ctrl_dec :
 forall s0 s3 : Site,
 ctrl_dec s0 s3 (bm (rec_inc_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then
   if eq_site_dec s3 owner
   then (ctrl_dec s0 s3 (bm c0) + 1)%Z
   else ctrl_dec s0 s3 (bm c0)
  else ctrl_dec s0 s3 (bm c0)).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 case (eq_site_dec s0 s2); intro.
 case (eq_site_dec s3 owner); intro.
 rewrite e; rewrite e0; rewrite post_card_mess.
 rewrite diff_collect_card_mess.
 trivial.

 apply diff_or_elsewhere with (m := inc_dec s2); [ trivial | discriminate ].

 rewrite diff_post_card_mess.
 apply diff_collect_card_mess.

 apply diff_or_elsewhere with (m := inc_dec s2); [ trivial | discriminate ].

 auto.

 rewrite diff_post_card_mess.
 apply diff_collect_card_mess; auto.

 apply diff_or_elsewhere with (m := inc_dec s2); [ trivial | discriminate ].

 auto.
Qed.

Lemma rinc_trans_ctrl_inc :
 forall s0 s3 : Site,
 ctrl_inc s0 s3 (bm (rec_inc_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then
   if eq_site_dec s3 s1
   then (ctrl_inc s0 s3 (bm c0) - 1)%Z
   else ctrl_inc s0 s3 (bm c0)
  else ctrl_inc s0 s3 (bm c0)).
Proof.
 intros; unfold ctrl_inc in |- *; simpl in |- *.
 case (eq_site_dec s0 s2); intro.
 case (eq_site_dec s3 s1); intro.
 rewrite e; rewrite e0; rewrite diff_post_card_mess.
 apply collect_card_mess; trivial.

 left; discriminate.

 rewrite diff_post_card_mess.
 apply diff_collect_card_mess; auto.

 left; discriminate.

 rewrite diff_post_card_mess.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := inc_dec s2);
  [ trivial | injection; auto ].

 left; discriminate.
Qed.

Remark rinc_trans_sigma_copy :
 forall s0 : Site,
 sigma_ctrl_copy s0 (bm (rec_inc_trans c0 s1 s2)) =
 sigma_ctrl_copy s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 apply sigma_simpl; intros; apply rinc_trans_ctrl_copy.
Qed.

Remark rinc_trans_sigma_dec :
 forall s0 : Site,
 sigma_ctrl_dec s0 (bm (rec_inc_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then (sigma_ctrl_dec s0 (bm c0) + 1)%Z
  else sigma_ctrl_dec s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 case (eq_site_dec s0 s2); intro.
 apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := owner).
 exact finite_site.

 rewrite rinc_trans_ctrl_dec; rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rinc_trans_ctrl_dec; rewrite e; rewrite case_eq;
  apply case_ineq; auto.

 apply sigma_simpl; intros; rewrite rinc_trans_ctrl_dec; apply case_ineq;
  auto.
Qed.

Remark rinc_trans_sigma_inc :
 forall s0 : Site,
 sigma_ctrl_inc s0 (bm (rec_inc_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then (sigma_ctrl_inc s0 (bm c0) - 1)%Z
  else sigma_ctrl_inc s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 case (eq_site_dec s0 s2); intro.
 apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s1).
 exact finite_site.

 rewrite rinc_trans_ctrl_inc; rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rinc_trans_ctrl_inc; rewrite e; rewrite case_eq;
  apply case_ineq; auto.

 apply sigma_simpl; intros; rewrite rinc_trans_ctrl_inc; apply case_ineq;
  auto.
Qed.

Lemma rinc_trans_sigma_ctrl :
 forall s0 : Site,
 sigma_ctrl s0 (bm (rec_inc_trans c0 s1 s2)) = sigma_ctrl s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite rinc_trans_sigma_copy.
 rewrite rinc_trans_sigma_dec.
 rewrite rinc_trans_sigma_inc.
 case (eq_site_dec s0 s2); intro.
 omega.

 trivial.
Qed.

End REC_INC_CTRL.

Section REC_INC_XY.

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis
  first_mess : first Message (bm c0 s1 owner) = value Message (inc_dec s2).

Hypothesis not_owner : s2 <> owner.

Remark rinc_trans_xi :
 forall s0 : Site, xi (rec_inc_trans c0 s1 s2) s0 = xi c0 s0.
Proof.
 intro; unfold xi in |- *.
 rewrite rinc_trans_ctrl_copy.
 rewrite rinc_trans_ctrl_dec.
 simpl in |- *; rewrite case_ineq; auto.

 trivial.

 trivial.
Qed.

Remark rinc_trans_yi :
 forall s0 : Site,
 yi (rec_inc_trans c0 s1 s2) s0 =
 (if eq_site_dec s0 s1 then (yi c0 s0 - 1)%Z else yi c0 s0).
Proof.
 intro; unfold yi in |- *.
 case (eq_site_dec s0 s1); intro.
 apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite rinc_trans_ctrl_inc.
 rewrite e; rewrite case_eq; apply case_eq.

 trivial.

 intros; rewrite rinc_trans_ctrl_inc.
 apply case_ineq; trivial.

 trivial.

 apply sigma_simpl; intros; rewrite rinc_trans_ctrl_inc.
 case (eq_site_dec x s2); intro.
 apply case_ineq; auto.

 trivial.

 trivial.
Qed.

Lemma rinc_trans_sigma_xi : sigma_xi (rec_inc_trans c0 s1 s2) = sigma_xi c0.
Proof.
 unfold sigma_xi in |- *; apply sigma_simpl; intros; apply rinc_trans_xi.
Qed.

Lemma rinc_trans_sigma_yi :
 sigma_yi (rec_inc_trans c0 s1 s2) = (sigma_yi c0 - 1)%Z.
Proof.
 unfold sigma_yi in |- *;
  apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s1).
 exact finite_site.

 rewrite rinc_trans_yi; apply case_eq.

 intros; rewrite rinc_trans_yi; apply case_ineq; trivial.
Qed.

End REC_INC_XY.

Section REC_INC_ALT.

(* structure de file d'attente *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Hypothesis s2_not_owner : s2 <> owner.

Lemma rinc_trans_D :
 D_queue (bm c0 s0 owner) -> D_queue (bm (rec_inc_trans c0 s1 s2) s0 owner).
Proof.
 intros; simpl in |- *; apply D_post_elsewhere.
 auto.

 apply D_collect; trivial.
Qed.

Lemma rinc_trans_alt :
 alternate (bm c0 s0 owner) ->
 alternate (bm (rec_inc_trans c0 s1 s2) s0 owner).
Proof.
 intros; simpl in |- *; apply alt_post_elsewhere.
 auto.

 apply alt_collect; trivial.
Qed.

End REC_INC_ALT.

Section REC_INC_RELAT.

(* sur la relation parent *)

Variable c0 : Config.

Variable s1 s2 : Site.

Remark rinc_trans_parent :
 forall s3 s4 : Site,
 parent (rec_inc_trans c0 s1 s2) s4 s3 -> parent c0 s4 s3.
Proof.
 intros; elim H.
 intros; apply parent_intro.
 apply rinc_trans_in_queue with (s1 := s1) (s2 := s2); trivial.
Qed.

Lemma rinc_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (rec_inc_trans c0 s1 s2) s3 s4 ->
 dt (rec_inc_trans c0 s1 s2) s3 < dt (rec_inc_trans c0 s1 s2) s4.
Proof.
 simpl in |- *; intros; apply H.
 apply rinc_trans_parent; trivial.
Qed.

End REC_INC_RELAT.
