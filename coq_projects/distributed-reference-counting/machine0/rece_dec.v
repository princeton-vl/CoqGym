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


(* RECEIVE DEC *)

(*definit la transition receive dec et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_REC_DEC.

Definition rec_dec_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (S (time c)) (dt c) (Dec_send_table (st c) s2) 
    (rt c) (Collect_message (bm c) s1 s2). 

End DEF_REC_DEC.

Section REC_DEC_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Lemma rdec_trans_le_dt_time :
 dt c0 s0 <= time c0 ->
 dt (rec_dec_trans c0 s1 s2) s0 <= time (rec_dec_trans c0 s1 s2).
Proof.
 simpl in |- *; auto.
Qed.

Lemma rdec_trans_diff_site :
 forall s3 s4 : Site,
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (rec_dec_trans c0 s1 s2) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; apply H.
 apply in_collect with (s1 := s1) (s2 := s2); trivial.
Qed.

Lemma rdec_trans_st :
 st (rec_dec_trans c0 s1 s2) s0 =
 (if eq_site_dec s0 s2 then (st c0 s0 - 1)%Z else st c0 s0).
Proof.
 simpl in |- *; case (eq_site_dec s0 s2); intro.
 rewrite e; apply pred_dec_send_table.

 apply no_dec_send_table; auto.
Qed.

Lemma rdec_trans_in_queue :
 forall s3 s4 : Site,
 In_queue Message (inc_dec s0) (bm (rec_dec_trans c0 s1 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 simpl in |- *; intros.
 apply in_collect with (s1 := s1) (s2 := s2); auto.
Qed.

Lemma rdec_trans_st_rt :
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (rec_dec_trans c0 s1 s2) s0 > 0)%Z ->
 rt (rec_dec_trans c0 s1 s2) s0 = true.
Proof.
 rewrite rdec_trans_st; simpl in |- *; case (eq_site_dec s0 s2); intro.
 intros; apply H; omega.

 auto.
Qed.

End REC_DEC_EFFECT.

Section REC_DEC_CTRL.

(* decompte de messages *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Hypothesis first_mess : first Message (bm c0 s1 s2) = value Message dec.

Lemma rdec_trans_ctrl_copy :
 forall s3 : Site,
 ctrl_copy s0 s3 (bm (rec_dec_trans c0 s1 s2)) = ctrl_copy s0 s3 (bm c0).
Proof.
 intros; unfold ctrl_copy in |- *; simpl in |- *.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := dec); [ trivial | discriminate ].
Qed.

Lemma rdec_trans_ctrl_dec :
 forall s3 : Site,
 ctrl_dec s0 s3 (bm (rec_dec_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then
  if eq_site_dec s3 s1
   then (ctrl_dec s0 s3 (bm c0) - 1)%Z
   else ctrl_dec s0 s3 (bm c0)
  else ctrl_dec s0 s3 (bm c0)).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 case (eq_site_dec s0 s2); intro.
 case (eq_site_dec s3 s1); intro.
 rewrite e; rewrite e0; apply collect_card_mess; trivial.

 apply diff_collect_card_mess; auto.

 apply diff_collect_card_mess; auto.
Qed.

Lemma rdec_trans_ctrl_inc :
 forall s3 : Site,
 ctrl_inc s0 s3 (bm (rec_dec_trans c0 s1 s2)) = ctrl_inc s0 s3 (bm c0).
Proof.
 intros; unfold ctrl_inc in |- *; simpl in |- *.
 apply diff_collect_card_mess.
 apply diff_or_elsewhere with (m := dec); [ trivial | discriminate ].
Qed.

Remark rdec_trans_sigma_copy :
 sigma_ctrl_copy s0 (bm (rec_dec_trans c0 s1 s2)) =
 sigma_ctrl_copy s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 apply sigma_simpl; intros; apply rdec_trans_ctrl_copy.
Qed.

Remark rdec_trans_sigma_dec :
 sigma_ctrl_dec s0 (bm (rec_dec_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then (sigma_ctrl_dec s0 (bm c0) - 1)%Z
  else sigma_ctrl_dec s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 case (eq_site_dec s0 s2); intro.
 apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s1).
 exact finite_site.

 rewrite rdec_trans_ctrl_dec.
 rewrite e; do 2 rewrite case_eq; trivial.

 intros; rewrite rdec_trans_ctrl_dec.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl; intros; rewrite rdec_trans_ctrl_dec.
 apply case_ineq; trivial.
Qed.

Remark rdec_trans_sigma_inc :
 sigma_ctrl_inc s0 (bm (rec_dec_trans c0 s1 s2)) = sigma_ctrl_inc s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 apply sigma_simpl; intros; apply rdec_trans_ctrl_inc.
Qed.

Lemma rdec_trans_sigma_ctrl :
 sigma_ctrl s0 (bm (rec_dec_trans c0 s1 s2)) =
 (if eq_site_dec s0 s2
  then (sigma_ctrl s0 (bm c0) - 1)%Z
  else sigma_ctrl s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite rdec_trans_sigma_copy.
 rewrite rdec_trans_sigma_dec.
 rewrite rdec_trans_sigma_inc.
 case (eq_site_dec s0 s2); intro.
 omega.

 trivial.
Qed.

End REC_DEC_CTRL.

Section REC_DEC_XY.

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis first_mess : first Message (bm c0 s1 s2) = value Message dec.

Remark rdec_trans_xi :
 forall s0 : Site,
 xi (rec_dec_trans c0 s1 s2) s0 =
 (if eq_site_dec owner s2
  then
   if eq_site_dec s0 s1 then (xi c0 s0 - 1)%Z else xi c0 s0
  else xi c0 s0).
Proof.
 intro; unfold xi in |- *.
 rewrite rdec_trans_ctrl_copy.
 rewrite rdec_trans_ctrl_dec.
 simpl in |- *; case (eq_site_dec owner s2); intro.
 case (eq_site_dec s0 s1); intro.
 omega.

 trivial.

 trivial.

 trivial.

 trivial.
Qed.

Remark rdec_trans_yi :
 forall s0 : Site, yi (rec_dec_trans c0 s1 s2) s0 = yi c0 s0.
Proof.
 intro; unfold yi in |- *; apply sigma_simpl.
 intros; apply rdec_trans_ctrl_inc; trivial.
Qed.

Lemma rdec_trans_sigma_xi :
 sigma_xi (rec_dec_trans c0 s1 s2) =
 (if eq_site_dec owner s2
  then (sigma_xi c0 - 1)%Z
  else sigma_xi c0).
Proof.
 unfold sigma_xi in |- *; case (eq_site_dec owner s2); intro.
 apply sigma__pred with (eq_E_dec := eq_site_dec) (x0 := s1).
 exact finite_site.

 rewrite rdec_trans_xi.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite rdec_trans_xi.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl.
 intros; rewrite rdec_trans_xi.
 apply case_ineq; trivial.
Qed.

Lemma rdec_trans_sigma_yi : sigma_yi (rec_dec_trans c0 s1 s2) = sigma_yi c0.
Proof.
 unfold sigma_yi in |- *; apply sigma_simpl; intros; apply rdec_trans_yi.
Qed.

End REC_DEC_XY.

Section REC_DEC_ALT.

(* structure de file *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Lemma rdec_trans_D :
 D_queue (bm c0 s0 owner) -> D_queue (bm (rec_dec_trans c0 s1 s2) s0 owner).
Proof.
 simpl in |- *; intros; apply D_collect; trivial.
Qed.

Lemma rdec_trans_alt :
 alternate (bm c0 s0 owner) ->
 alternate (bm (rec_dec_trans c0 s1 s2) s0 owner).
Proof.
 intros; simpl in |- *; apply alt_collect; trivial.
Qed.

End REC_DEC_ALT.

Section REC_DEC_RELAT.

(* relation parent *)

Variable c0 : Config.

Variable s1 s2 : Site.

Remark rdec_trans_parent :
 forall s3 s4 : Site,
 parent (rec_dec_trans c0 s1 s2) s4 s3 -> parent c0 s4 s3.
Proof.
 intros; elim H.
 intros; apply parent_intro.
 apply rdec_trans_in_queue with (s1 := s1) (s2 := s2); trivial.
Qed.

Lemma rdec_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (rec_dec_trans c0 s1 s2) s3 s4 ->
 dt (rec_dec_trans c0 s1 s2) s3 < dt (rec_dec_trans c0 s1 s2) s4.
Proof.
 simpl in |- *; intros; apply H.
 apply rdec_trans_parent; trivial.
Qed.

End REC_DEC_RELAT.
