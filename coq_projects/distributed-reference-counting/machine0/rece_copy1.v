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


(* RECEIVE 1 *)

(*definit la premiere transition receive copy et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_REC_COP1.

Definition rec_copy1_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (S (time c)) (dt c) (st c) (rt c)
    (Post_message dec (Collect_message (bm c) s1 s2) s2 s1). 

End DEF_REC_COP1.

Section REC_COP1_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s1 s2 : Site.

Lemma rcop1_trans_le_dt_time :
 forall s0 : Site,
 dt c0 s0 <= time c0 ->
 dt (rec_copy1_trans c0 s1 s2) s0 <= time (rec_copy1_trans c0 s1 s2).
Proof.
 simpl in |- *; auto.
Qed.

Lemma rcop1_trans_diff_site :
 forall s3 s4 : Site,
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (rec_copy1_trans c0 s1 s2) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; apply H.
 apply in_collect with (s1 := s1) (s2 := s2).
 apply in_post with (m' := dec) (s1 := s2) (s2 := s1).
 discriminate.

 trivial.
Qed.

Lemma rcop1_trans_in_queue :
 forall s0 s3 s4 : Site,
 In_queue Message (inc_dec s0) (bm (rec_copy1_trans c0 s1 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 simpl in |- *; intros.
 apply in_collect with (s1 := s1) (s2 := s2).
 apply in_post with (m' := dec) (s1 := s2) (s2 := s1).
 discriminate.

 auto.
Qed.

Lemma rcop1_trans_st_rt :
 forall s0 : Site,
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (rec_copy1_trans c0 s1 s2) s0 > 0)%Z ->
 rt (rec_copy1_trans c0 s1 s2) s0 = true.
Proof.
 simpl in |- *; intros; auto.
Qed.

End REC_COP1_EFFECT.

Section REC_COP1_CTRL.

(* decompte de messages *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Hypothesis first_mess : first Message (bm c0 s1 s2) = value Message copy.

Lemma rcop1_trans_ctrl_copy :
 forall s3 : Site,
 ctrl_copy s0 s3 (bm (rec_copy1_trans c0 s1 s2)) =
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

 apply diff_collect_card_mess; auto.

 apply diff_collect_card_mess; auto.

 left; discriminate.
Qed.

Lemma rcop1_trans_ctrl_dec :
 forall s3 : Site,
 ctrl_dec s0 s3 (bm (rec_copy1_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then
   
   if eq_site_dec s3 s2
   then  (ctrl_dec s0 s3 (bm c0) + 1)%Z
   else  ctrl_dec s0 s3 (bm c0)
  else  ctrl_dec s0 s3 (bm c0)).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 case (eq_site_dec s0 s1); intro.
 case (eq_site_dec s3 s2); intro.
 rewrite e; rewrite e0; rewrite post_card_mess.
 rewrite diff_collect_card_mess.
 auto.

 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 rewrite diff_post_card_mess.
 rewrite diff_collect_card_mess.
 auto.

 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 auto.

 rewrite diff_post_card_mess.
 rewrite diff_collect_card_mess.
 auto.

 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 auto.
Qed.

Lemma rcop1_trans_ctrl_inc :
 forall s3 : Site,
 ctrl_inc s0 s3 (bm (rec_copy1_trans c0 s1 s2)) = ctrl_inc s0 s3 (bm c0).
Proof.
 unfold ctrl_inc in |- *; simpl in |- *; intros.
 rewrite diff_post_card_mess.
 rewrite diff_collect_card_mess.
 auto.
 
 apply diff_or_elsewhere with (m := copy); [ trivial | discriminate ].

 left; discriminate.
Qed.

Remark rcop1_trans_sigma_copy :
 sigma_ctrl_copy s0 (bm (rec_copy1_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then  (sigma_ctrl_copy s0 (bm c0) - 1)%Z
  else  sigma_ctrl_copy s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 case (eq_site_dec s0 s1); intro.
 apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite rcop1_trans_ctrl_copy.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rcop1_trans_ctrl_copy.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl; intros; rewrite rcop1_trans_ctrl_copy.
 apply case_ineq; trivial.
Qed.

Remark rcop1_trans_sigma_dec :
 sigma_ctrl_dec s0 (bm (rec_copy1_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then  (sigma_ctrl_dec s0 (bm c0) + 1)%Z
  else  sigma_ctrl_dec s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 case (eq_site_dec s0 s1); intro.
 apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite rcop1_trans_ctrl_dec.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rcop1_trans_ctrl_dec.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl; intros; rewrite rcop1_trans_ctrl_dec.
 apply case_ineq; trivial.
Qed.

Remark rcop1_trans_sigma_inc :
 sigma_ctrl_inc s0 (bm (rec_copy1_trans c0 s1 s2)) =
 sigma_ctrl_inc s0 (bm c0).
Proof.
 unfold sigma_ctrl_inc in |- *; apply sigma_simpl; intros;
  apply rcop1_trans_ctrl_inc; auto.
Qed.

Lemma rcop1_trans_sigma_ctrl :
 sigma_ctrl s0 (bm (rec_copy1_trans c0 s1 s2)) = sigma_ctrl s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite rcop1_trans_sigma_copy.
 rewrite rcop1_trans_sigma_dec.
 rewrite rcop1_trans_sigma_inc.
 simpl in |- *; case (eq_site_dec s0 s1); intro; omega.
Qed.

End REC_COP1_CTRL.

Section REC_COP1_XY.

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis first_mess : first Message (bm c0 s1 s2) = value Message copy.

Remark rcop1_trans_xi :
 forall s0 : Site, xi (rec_copy1_trans c0 s1 s2) s0 = xi c0 s0.
Proof.
 intro; unfold xi in |- *.
 rewrite rcop1_trans_ctrl_copy.
 rewrite rcop1_trans_ctrl_dec.
 simpl in |- *; case (eq_site_dec owner s1); intro.
 case (eq_site_dec s0 s2); intro.
 omega.

 trivial.

 trivial.

 trivial.

 trivial.
Qed.

Remark rcop1_trans_yi :
 forall s0 : Site, yi (rec_copy1_trans c0 s1 s2) s0 = yi c0 s0.
Proof.
 intro; unfold yi in |- *; apply sigma_simpl.
 intros; apply rcop1_trans_ctrl_inc; trivial.
Qed.

Lemma rcop1_trans_sigma_xi :
 sigma_xi (rec_copy1_trans c0 s1 s2) = sigma_xi c0.
Proof.
 unfold sigma_xi in |- *; apply sigma_simpl; intros; apply rcop1_trans_xi.
Qed.

Lemma rcop1_trans_sigma_yi :
 sigma_yi (rec_copy1_trans c0 s1 s2) = sigma_yi c0.
Proof.
 unfold sigma_yi in |- *; apply sigma_simpl; intros; apply rcop1_trans_yi.
Qed.

End REC_COP1_XY.

Section REC_COP1_ALT.

(* structure de file d'attente *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Lemma rcop1_trans_D :
 D_queue (bm c0 s0 owner) -> D_queue (bm (rec_copy1_trans c0 s1 s2) s0 owner).
Proof.
 simpl in |- *; intros.
 case (eq_queue_dec s2 s0 s1 owner); intro.
 decompose [and] a; rewrite H0; rewrite H1.
 apply D_post_dec.

 apply D_post_elsewhere.
 trivial.

 apply D_collect; trivial.
Qed.

Lemma rcop1_trans_alt :
 alternate (bm c0 s0 owner) ->
 alternate (bm (rec_copy1_trans c0 s1 s2) s0 owner).
Proof.
 case (eq_queue_dec s2 s0 s1 owner); intros; simpl in |- *.
 decompose [and] a; rewrite H0; rewrite H1.
 apply alt_post_dec.
 apply alt_collect; trivial.

 apply alt_post_elsewhere.
 trivial.

 apply alt_collect; trivial.
Qed.

End REC_COP1_ALT.

Section REC_COP1_RELAT.

(* relation parent *)

Variable c0 : Config.

Variable s1 s2 : Site.

Remark rcop1_trans_parent :
 forall s3 s4 : Site,
 parent (rec_copy1_trans c0 s1 s2) s4 s3 -> parent c0 s4 s3.
Proof.
 intros; elim H.
 intros; apply parent_intro.
 apply rcop1_trans_in_queue with (s1 := s1) (s2 := s2); trivial.
Qed.

Lemma rcop1_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (rec_copy1_trans c0 s1 s2) s3 s4 ->
 dt (rec_copy1_trans c0 s1 s2) s3 < dt (rec_copy1_trans c0 s1 s2) s4.
Proof.
 simpl in |- *; intros; apply H.
 apply rcop1_trans_parent; trivial.
Qed.

End REC_COP1_RELAT.
