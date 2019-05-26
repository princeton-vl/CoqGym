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

(* RECEIVE COPY 3 *)

(*definit la troisiem transition receive copy et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_REC_COP3.

Definition rec_copy3_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (S (time c)) (Update_table (dt c) s2 (S (time c))) 
    (st c) (Set_rec_table (rt c) s2)
    (Post_message (inc_dec s1) (Collect_message (bm c) s1 s2) s2 owner). 

End DEF_REC_COP3.

Section REC_COP3_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s0 s1 s2 s3 s4 : Site.

Hypothesis rt_true : rt c0 s2 = false.

Lemma rcop3_trans_le_dt_time :
 dt c0 s0 <= time c0 ->
 dt (rec_copy3_trans c0 s1 s2) s0 <= time (rec_copy3_trans c0 s1 s2).
Proof.
 intros; simpl in |- *.
 case (eq_site_dec s2 s0); intro.
 rewrite e; rewrite update_here; trivial.

 rewrite update_elsewhere; auto.
Qed.

Lemma rcop3_trans_diff_site :
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (rec_copy3_trans c0 s1 s2) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; apply H.
 apply in_collect with (s1 := s1) (s2 := s2).
 apply in_post with (m' := inc_dec s1) (s1 := s2) (s2 := owner).
 discriminate.

 trivial.
Qed.

Lemma rcop3_trans_rt :
 Int (rt (rec_copy3_trans c0 s1 s2) s0) =
 (if eq_site_dec s0 s2
  then  (Int (rt c0 s0) + 1)%Z
  else  Int (rt c0 s0)).
Proof.
 case (eq_site_dec s0 s2); simpl in |- *; intros.
 rewrite e; apply S_set_rec_table; auto.
 apply no_set_rec_table; auto.
Qed.

Lemma rcop3_trans_in_queue :
 s0 <> s1 ->
 In_queue Message (inc_dec s0) (bm (rec_copy3_trans c0 s1 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 simpl in |- *; intros.
 apply in_collect with (s1 := s1) (s2 := s2).
 apply in_post with (m' := inc_dec s1) (s1 := s2) (s2 := owner).
 injection; auto.

 auto.
Qed.

Lemma rcop3_trans_in_other_queue :
 s2 <> s3 \/ s4 <> owner ->
 In_queue Message (inc_dec s0) (bm (rec_copy3_trans c0 s1 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 simpl in |- *; intros.
 apply in_collect with (s1 := s1) (s2 := s2).
 generalize H0; rewrite post_elsewhere.
 auto.

 elim H; auto.
Qed.

Lemma rcop3_trans_st_rt :
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (rec_copy3_trans c0 s1 s2) s0 > 0)%Z ->
 rt (rec_copy3_trans c0 s1 s2) s0 = true.
Proof.
 simpl in |- *; intros; auto.
 case (eq_site_dec s0 s2); intro.
 rewrite e; apply true_set_rec_table.

 rewrite inch_set_rec_table; auto.
Qed.

End REC_COP3_EFFECT.

Section REC_COP3_CTRL.

(* decompte de messages *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Hypothesis not_owner : s1 <> owner.

Hypothesis first_mess : first Message (bm c0 s1 s2) = value Message copy.

Lemma rcop3_trans_ctrl_copy :
 forall s3 : Site,
 ctrl_copy s0 s3 (bm (rec_copy3_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then
   
   if eq_site_dec s3 s2
   then  (ctrl_copy s0 s3 (bm c0) - 1)%Z
   else  ctrl_copy s0 s3 (bm c0)
  else  ctrl_copy s0 s3 (bm c0)).
Proof.
 intros; unfold ctrl_copy in |- *; simpl in |- *.
 rewrite diff_post_card_mess.
 case (eq_site_dec s0 s1); intro.
 case (eq_site_dec s3 s2); intro.
 rewrite e; rewrite e0; apply collect_card_mess; trivial.

 apply diff_collect_card_mess.
 auto.

 apply diff_collect_card_mess.
 auto.

 left; discriminate.
Qed.

Lemma rcop3_trans_ctrl_dec :
 forall s3 : Site,
 ctrl_dec s0 s3 (bm (rec_copy3_trans c0 s1 s2)) = ctrl_dec s0 s3 (bm c0).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 rewrite diff_post_card_mess.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 left; discriminate.
Qed.

Lemma rcop3_trans_ctrl_inc :
 forall s3 : Site,
 ctrl_inc s0 s3 (bm (rec_copy3_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then
   
   if eq_site_dec s3 s2
   then  (ctrl_inc s0 s3 (bm c0) + 1)%Z
   else  ctrl_inc s0 s3 (bm c0)
  else  ctrl_inc s0 s3 (bm c0)).
Proof.
 intros; unfold ctrl_inc in |- *; simpl in |- *.
 case (eq_site_dec s0 s1); intro.
 case (eq_site_dec s3 s2); intro.
 rewrite e; rewrite e0; rewrite post_card_mess.
 rewrite diff_collect_card_mess.
 trivial.

 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 rewrite diff_post_card_mess.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 auto.

 rewrite diff_post_card_mess.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 left; injection; auto.
Qed.

Remark rcop3_trans_sigma_copy :
 sigma_ctrl_copy s0 (bm (rec_copy3_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then  (sigma_ctrl_copy s0 (bm c0) - 1)%Z
  else  sigma_ctrl_copy s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 case (eq_site_dec s0 s1); intro.
 apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite rcop3_trans_ctrl_copy.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rcop3_trans_ctrl_copy.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl; intros; rewrite rcop3_trans_ctrl_copy.
 apply case_ineq; trivial.
Qed.

Remark rcop3_trans_sigma_dec :
 sigma_ctrl_dec s0 (bm (rec_copy3_trans c0 s1 s2)) =
 sigma_ctrl_dec s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 apply sigma_simpl; intros; apply rcop3_trans_ctrl_dec.
Qed.

Remark rcop3_trans_sigma_inc :
 sigma_ctrl_inc s0 (bm (rec_copy3_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then  (sigma_ctrl_inc s0 (bm c0) + 1)%Z
  else  sigma_ctrl_inc s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 case (eq_site_dec s0 s1); intro.
 apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite rcop3_trans_ctrl_inc.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rcop3_trans_ctrl_inc.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl; intros; rewrite rcop3_trans_ctrl_inc.
 apply case_ineq; trivial.
Qed.

Lemma rcop3_trans_sigma_ctrl :
 sigma_ctrl s0 (bm (rec_copy3_trans c0 s1 s2)) = sigma_ctrl s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite rcop3_trans_sigma_copy.
 rewrite rcop3_trans_sigma_dec.
 rewrite rcop3_trans_sigma_inc.
 case (eq_site_dec s0 s1); intro; omega.
Qed.

End REC_COP3_CTRL.

Section REC_COP3_XY.

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis rt_true : rt c0 s2 = false.

Hypothesis not_owner : s1 <> owner.

Hypothesis first_mess : first Message (bm c0 s1 s2) = value Message copy.

Remark rcop3_trans_xi :
 forall s0 : Site,
 xi (rec_copy3_trans c0 s1 s2) s0 =
 (if eq_site_dec s0 s2 then  (xi c0 s0 + 1)%Z else  xi c0 s0).
Proof.
 intro; unfold xi in |- *.
 rewrite rcop3_trans_ctrl_copy.
 rewrite case_ineq.
 rewrite rcop3_trans_ctrl_dec.
 rewrite rcop3_trans_rt.
 case (eq_site_dec s0 s2); intro.
 omega.

 trivial.

 trivial.

 trivial.

 auto.

 trivial.
Qed.

Remark rcop3_trans_yi :
 forall s0 : Site,
 yi (rec_copy3_trans c0 s1 s2) s0 =
 (if eq_site_dec s0 s2 then  (yi c0 s0 + 1)%Z else yi c0 s0).
Proof.
 intro; unfold yi in |- *.
 case (eq_site_dec s0 s2); intro.
 apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s1).
 exact finite_site.

 rewrite rcop3_trans_ctrl_inc.
 rewrite e; rewrite case_eq; apply case_eq.

 trivial.

 intros; rewrite rcop3_trans_ctrl_inc.
 apply case_ineq; trivial.

 trivial.

 apply sigma_simpl; intros; rewrite rcop3_trans_ctrl_inc.
 case (eq_site_dec x s1); intro.
 apply case_ineq; trivial.

 trivial.

 trivial.
Qed.

Lemma rcop3_trans_sigma_xi :
 sigma_xi (rec_copy3_trans c0 s1 s2) = (sigma_xi c0 + 1)%Z.
Proof.
 unfold sigma_xi in |- *;
  apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite (rcop3_trans_xi s2); apply case_eq.

 intros; rewrite rcop3_trans_xi; apply case_ineq; trivial.
Qed.

Lemma rcop3_trans_sigma_yi :
 sigma_yi (rec_copy3_trans c0 s1 s2) = (sigma_yi c0 + 1)%Z.
Proof.
 unfold sigma_yi in |- *;
  apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite rcop3_trans_yi; apply case_eq.

 intros; rewrite rcop3_trans_yi; apply case_ineq; trivial.
Qed.

End REC_COP3_XY.

Section REC_COP3_ALT.

(* structure de file d'attente *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Hypothesis rt_true : rt c0 s2 = false.

Hypothesis not_owner : s1 <> owner.

Lemma rcop3_trans_D :
 (rt c0 s0 = false -> D_queue (bm c0 s0 owner)) ->
 rt (rec_copy3_trans c0 s1 s2) s0 = false ->
 D_queue (bm (rec_copy3_trans c0 s1 s2) s0 owner).
Proof.
 case (eq_site_dec s0 s2); intro; simpl in |- *.
 rewrite e; rewrite true_set_rec_table; intros; discriminate H0.

 rewrite inch_set_rec_table.
 intros; apply D_post_elsewhere.
 auto.

 apply D_collect; auto.

 auto.
Qed.

Lemma rcop3_trans_alt :
 D_queue (bm c0 s2 owner) ->
 alternate (bm c0 s0 owner) ->
 alternate (bm (rec_copy3_trans c0 s1 s2) s0 owner).
Proof.
 case (eq_site_dec s2 s0); intros; simpl in |- *.
 rewrite e; apply alt_post_inc.
 apply alt_collect; trivial.

 rewrite collect_elsewhere.
 rewrite e in H; elim H; auto.

 case (eq_site_dec s1 s0); intro.
 rewrite e0 in not_owner; auto.

 auto.

 apply alt_post_elsewhere.
 auto.

 apply alt_collect; trivial.
Qed.

End REC_COP3_ALT.

Section REC_COP3_RELAT.

(* relation parent *)

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis diff_site : s1 <> s2.

Hypothesis rt_true : rt c0 s2 = false.

Hypothesis
  ancestor_rt : forall s1 s2 : Site, ancestor c0 s2 s1 -> rt c0 s2 = true.

Hypothesis le_dt_time : forall s0 : Site, dt c0 s0 <= time c0.

Remark no_ancestor_s2 : forall s : Site, ~ ancestor c0 s2 s.
Proof.
 intro; red in |- *; intro; absurd (false = rt c0 s2).
 apply true_not_false; apply (ancestor_rt s); trivial.

 auto.
Qed.

Remark rcop3_trans_parent :
 forall s3 s4 : Site,
 s1 <> s4 \/ s2 <> s3 ->
 parent (rec_copy3_trans c0 s1 s2) s4 s3 -> parent c0 s4 s3.
Proof.
 intros; generalize H; elim H0.
 intros; apply parent_intro.
 decompose [or] H2.
 apply rcop3_trans_in_queue with (s1 := s1) (s2 := s2); auto.

 apply rcop3_trans_in_other_queue with (s1 := s1) (s2 := s2); auto.
Qed.

Remark rcop3_trans_no_parent :
 forall s3 s4 : Site,
 s1 <> s4 \/ s2 <> s3 ->
 ~ parent c0 s4 s3 -> ~ parent (rec_copy3_trans c0 s1 s2) s4 s3.
Proof.
 intros; red in |- *; intro; elim H0.
 apply rcop3_trans_parent; trivial.
Qed.

Lemma rcop3_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (rec_copy3_trans c0 s1 s2) s3 s4 ->
 dt (rec_copy3_trans c0 s1 s2) s3 < dt (rec_copy3_trans c0 s1 s2) s4.
Proof.
 simpl in |- *; intros.
 case (eq_site_dec s2 s3); intro.
 absurd (parent (rec_copy3_trans c0 s1 s2) s2 s4).
 apply rcop3_trans_no_parent.
 auto.

 red in |- *; intro.
 elim (no_ancestor_s2 s4); apply short; trivial.

 rewrite <- e in H0; trivial.

 rewrite update_elsewhere.
 case (eq_site_dec s2 s4); intro.
 rewrite e; rewrite update_here.
 generalize (le_dt_time s3); omega.

 rewrite update_elsewhere.
 apply H; apply rcop3_trans_parent; auto.

 trivial.

 trivial.
Qed.

End REC_COP3_RELAT.
