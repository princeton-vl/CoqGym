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


(* COPY *)

(*definit la transition copy et ses consequences*)

Require Export init.
Require Export table_act.
Require Export mess_act.

Unset Standard Proposition Elimination Names.

Section DEF_COPY.

Definition copy_trans (c : Config) (s1 s2 : Site) :=
  mkconfig (S (time c)) (dt c) (Inc_send_table (st c) s1) 
    (rt c) (Post_message copy (bm c) s1 s2). 

End DEF_COPY.

Section COPY_EFFECT.

(* invariants *)

Variable c0 : Config.

Variable s1 s2 : Site.

Hypothesis diff_s1_s2 : s1 <> s2.

Lemma copy_trans_le_dt_time :
 forall s0 : Site,
 dt c0 s0 <= time c0 ->
 dt (copy_trans c0 s1 s2) s0 <= time (copy_trans c0 s1 s2).
Proof.
 simpl in |- *; auto.
Qed.

Lemma copy_trans_diff_site :
 forall s3 s4 : Site,
 (In_queue Message copy (bm c0 s3 s4) -> s3 <> s4) ->
 In_queue Message copy (bm (copy_trans c0 s1 s2) s3 s4) -> s3 <> s4.
Proof.
 simpl in |- *; intros; case (eq_queue_dec s1 s3 s2 s4); intro.
 decompose [and] a; rewrite <- H1; rewrite <- H2; trivial.

 generalize H0; rewrite post_elsewhere; auto.
Qed.

Lemma copy_trans_st :
 forall s0 : Site,
 st (copy_trans c0 s1 s2) s0 =
 (if eq_site_dec s0 s1 then  (st c0 s0 + 1)%Z else  st c0 s0).
Proof.
 intro; simpl in |- *; case (eq_site_dec s0 s1); intro.
 rewrite e; apply S_inc_send_table.

 apply no_inc_send_table; auto.
Qed.

Lemma copy_trans_in_queue :
 forall s0 s3 s4 : Site,
 In_queue Message (inc_dec s0) (bm (copy_trans c0 s1 s2) s3 s4) ->
 In_queue Message (inc_dec s0) (bm c0 s3 s4).
Proof.
 intros; apply in_post with (m' := copy) (s1 := s1) (s2 := s2).
 discriminate.

 auto.
Qed.

Lemma copy_trans_st_rt :
 forall s0 : Site,
 s0 <> owner ->
 access s1 (rt c0) ->
 ((st c0 s0 > 0)%Z -> rt c0 s0 = true) ->
 (st (copy_trans c0 s1 s2) s0 > 0)%Z -> rt (copy_trans c0 s1 s2) s0 = true.
Proof.
 intro; rewrite copy_trans_st; simpl in |- *; case (eq_site_dec s0 s1); intro.
 unfold access in |- *; rewrite <- e; intros; elim H0; intro.
 absurd (s0 = owner); trivial.

 trivial.

 auto.
Qed.

End COPY_EFFECT.

Section COPY_CTRL.

(* decompte de messages *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Lemma copy_trans_ctrl_copy :
 forall s' : Site,
 ctrl_copy s0 s' (bm (copy_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then
   
   if eq_site_dec s' s2
   then  (ctrl_copy s0 s' (bm c0) + 1)%Z
   else  ctrl_copy s0 s' (bm c0)
  else  ctrl_copy s0 s' (bm c0)).
Proof.
 intros; unfold ctrl_copy in |- *; simpl in |- *.
 case (eq_site_dec s0 s1); intro.
 case (eq_site_dec s' s2); intro.
 rewrite e; rewrite e0; apply post_card_mess.

 apply diff_post_card_mess; auto.

 apply diff_post_card_mess; auto.
Qed.

Lemma copy_trans_ctrl_dec :
 forall s' : Site,
 ctrl_dec s0 s' (bm (copy_trans c0 s1 s2)) = ctrl_dec s0 s' (bm c0).
Proof.
 intros; unfold ctrl_dec in |- *; simpl in |- *.
 apply diff_post_card_mess.
 left; discriminate.
Qed.

Lemma copy_trans_ctrl_inc :
 forall s' : Site,
 ctrl_inc s0 s' (bm (copy_trans c0 s1 s2)) = ctrl_inc s0 s' (bm c0).
Proof.
 intros; unfold ctrl_inc in |- *; simpl in |- *.
 apply diff_post_card_mess.
 left; discriminate.
Qed.

Remark copy_trans_sigma_copy :
 sigma_ctrl_copy s0 (bm (copy_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then  (sigma_ctrl_copy s0 (bm c0) + 1)%Z
  else  sigma_ctrl_copy s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl_copy in |- *.
 case (eq_site_dec s0 s1); intro.
 apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite copy_trans_ctrl_copy.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite copy_trans_ctrl_copy.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl.
 intros; rewrite copy_trans_ctrl_copy.
 apply case_ineq; trivial.
Qed.

Remark copy_trans_sigma_dec :
 sigma_ctrl_dec s0 (bm (copy_trans c0 s1 s2)) = sigma_ctrl_dec s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_dec in |- *.
 apply sigma_simpl; intros; apply copy_trans_ctrl_dec.
Qed.

Remark copy_trans_sigma_inc :
 sigma_ctrl_inc s0 (bm (copy_trans c0 s1 s2)) = sigma_ctrl_inc s0 (bm c0).
Proof.
 intros; unfold sigma_ctrl_inc in |- *.
 apply sigma_simpl; intros; apply copy_trans_ctrl_inc.
Qed.

Lemma copy_trans_sigma_ctrl :
 sigma_ctrl s0 (bm (copy_trans c0 s1 s2)) =
 (if eq_site_dec s0 s1
  then  (sigma_ctrl s0 (bm c0) + 1)%Z
  else  sigma_ctrl s0 (bm c0)).
Proof.
 intros; unfold sigma_ctrl in |- *.
 rewrite copy_trans_sigma_copy.
 rewrite copy_trans_sigma_dec.
 rewrite copy_trans_sigma_inc.
 case (eq_site_dec s0 s1); intro.
 omega.

 trivial.
Qed.

End COPY_CTRL.

Section COPY_XY.

Variable c0 : Config.

Variable s1 s2 : Site.

Remark copy_trans_xi :
 forall s0 : Site,
 xi (copy_trans c0 s1 s2) s0 =
 (if eq_site_dec owner s1
  then
   
   if eq_site_dec s0 s2 then  (xi c0 s0 + 1)%Z else  xi c0 s0
  else  xi c0 s0).
Proof.
 intro; unfold xi in |- *.
 rewrite copy_trans_ctrl_copy.
 rewrite copy_trans_ctrl_dec.
 simpl in |- *; case (eq_site_dec owner s1); intro.
 case (eq_site_dec s0 s2); intro.
 omega.

 trivial.

 trivial.
Qed.

Remark copy_trans_yi :
 forall s0 : Site, yi (copy_trans c0 s1 s2) s0 = yi c0 s0.
Proof.
 intro; unfold yi in |- *; apply sigma_simpl.
 intros; apply copy_trans_ctrl_inc.
Qed.

Lemma copy_trans_sigma_xi :
 sigma_xi (copy_trans c0 s1 s2) =
 (if eq_site_dec owner s1
  then  (sigma_xi c0 + 1)%Z
  else  sigma_xi c0).
Proof.
 unfold sigma_xi in |- *.
 case (eq_site_dec owner s1); intro.
 apply sigma__S with (eq_E_dec := eq_site_dec) (x0 := s2).
 exact finite_site.

 rewrite copy_trans_xi.
 rewrite e; rewrite case_eq; apply case_eq.

 intros; rewrite copy_trans_xi.
 rewrite e; rewrite case_eq; apply case_ineq; trivial.

 apply sigma_simpl; intros.
 rewrite copy_trans_xi; apply case_ineq; trivial.
Qed.

Lemma copy_trans_sigma_yi : sigma_yi (copy_trans c0 s1 s2) = sigma_yi c0.
Proof.
 unfold sigma_yi in |- *; apply sigma_simpl; intros; apply copy_trans_yi.
Qed.

End COPY_XY.

Section COPY_ALT.

(* structure de file d'attente *)

Variable c0 : Config.

Variable s0 s1 s2 : Site.

Hypothesis s2_not_owner : s2 <> owner.

Lemma copy_trans_D :
 D_queue (bm c0 s0 owner) -> D_queue (bm (copy_trans c0 s1 s2) s0 owner).
Proof.
 intros; simpl in |- *; apply D_post_elsewhere; auto.
Qed.

Lemma copy_trans_alt :
 alternate (bm c0 s0 owner) -> alternate (bm (copy_trans c0 s1 s2) s0 owner).
Proof.
 intros; simpl in |- *; apply alt_post_elsewhere; auto.
Qed.

End COPY_ALT.

Section COPY_RELAT.

(* relation parent *)

Variable c0 : Config.

Variable s1 s2 : Site.

Remark copy_trans_parent :
 forall s3 s4 : Site, parent (copy_trans c0 s1 s2) s4 s3 -> parent c0 s4 s3.
Proof.
 intros; elim H.
 intros; apply parent_intro.
 apply copy_trans_in_queue with (s1 := s1) (s2 := s2); trivial.
Qed.

Lemma copy_trans_parent_cr :
 forall s3 s4 : Site,
 (parent c0 s3 s4 -> dt c0 s3 < dt c0 s4) ->
 parent (copy_trans c0 s1 s2) s3 s4 ->
 dt (copy_trans c0 s1 s2) s3 < dt (copy_trans c0 s1 s2) s4.
Proof.
 simpl in |- *; intros; apply H.
 apply copy_trans_parent; trivial.
Qed.

End COPY_RELAT.
