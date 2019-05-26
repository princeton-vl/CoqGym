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


Require Export DistributedReferenceCounting.machine1.invariant6.

Unset Standard Proposition Elimination Names.

Lemma parent_invariant_inductive :
 forall (c : Config) (t : class_trans c),
 legal c ->
 (legal c ->
  forall s : Site,
  indirect_son1 c s -> exists s1 : Site, direct_son c s1 /\ ancestor c s1 s) ->
 legal (transition c t) ->
 forall s : Site,
 indirect_son1 (transition c t) s ->
 exists s1 : Site,
   direct_son (transition c t) s1 /\ ancestor (transition c t) s1 s.

Proof.
  
  simple induction t.
  
  (*  1 *)
  
  
  simpl in |- *.
  intros s1 s2 n n0 a H H0 Hnext.
intros.
  elim (H0 H s).
  intros.
  split with x.
  decompose [and] H2.
  split.
  elim H3; intros; apply direct_son_intro; auto.
  simpl in |- *; auto.
  intros.
  apply inc_dec_not_in_post.
  auto.
  
  intro.
  discriminate.
  
  elim H4.
  intros.
  apply short.
  elim H5.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply inc_dec_in_post.
  auto.
  
  intro; discriminate.
  
  intros.
  apply (long (copy_trans c s1 s2) s0 s3 s4).
  auto.
  
  elim H7.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply inc_dec_in_post.
  auto.
  
  intro; discriminate.
  
  apply indirect_son1_intro.
  elim H1.
  intros.
  auto.
  
  elim H1.
  intros.
  generalize H3.
  simpl in |- *.
  auto.
  
  elim H1.
  intros.
  generalize H4.
  simpl in |- *.
  case (eq_queue_dec s1 s0 s2 owner).
  intro.
  decompose [and] a0.
  rewrite H5; rewrite H6.
  rewrite post_here.
  simpl in |- *.
  auto.
  
  intro.
  rewrite post_elsewhere.
  auto.
  
  auto.
  
  
  
  (*  2  *)
  
  simpl in |- *.
  intros s1 s2 e H H0 Hnext; intros.
  elim (H0 H s).
  intros.
  split with x.
  decompose [and] H2.
  split.
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; auto.
  
  simpl in |- *.
  intros.
  apply inc_dec_not_in_collect with (m := dec).
  auto.
  
  auto.
  
  discriminate.
  
  elim H4.
  intros.
  apply short.
  apply parent_intro.
  simpl in |- *.
  elim H5.
  auto.
  
  simpl in |- *.
  apply inc_dec_in_collect with (m := dec).
  auto.
  
  elim H5.
  auto.
  
  discriminate.
  
  intros.
  apply (long (rec_dec_trans c s1 s2) s0 s3 s4).
  auto.
  
  elim H7.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *; apply inc_dec_in_collect with (m := dec).
  auto.
  
  auto.
  
  discriminate.
  
  elim H1.
  intros.
  apply indirect_son1_intro.
  auto.
  
  generalize H3.
  simpl in |- *.
  auto.
  
  generalize H4.
  simpl in |- *.
  case (eq_queue_dec s1 s0 s2 owner).
  intro.
  decompose [and] a.
  rewrite H6; rewrite H5.
  rewrite collect_here.
  unfold not in |- *.
  intros.
  elim H7.
  intro.
  generalize (inc_dec_not_in_first_out (bm c s0 owner) dec s3).
  unfold not in |- *.
  intro.
  intro.
  apply H9.
  auto.
  auto.
  rewrite <- H6; rewrite <- H5; auto.
  
  discriminate.
  
  generalize (H8 s3).
  auto.
  
  auto.
  
  intro.
  rewrite collect_elsewhere.
  auto.
  
  auto.
  
  
  (* 3 *)
  
  
  simpl in |- *.
  intros s1 s3 e H H0 Hnext; intros.
  
  elim (decide_rt c s1).
  
  intro.
  elim (H0 H s).
  intros.
  decompose [and] H2.
  split with x.
  split.
  elim H3; intros; apply direct_son_intro; auto.
  simpl in |- *.
  rewrite post_elsewhere.
  rewrite collect_elsewhere.
  auto.
  
  left.
  generalize (not_inc_dec_in (bm c s0 owner) H7).
  intro.
  unfold not in |- *; intro.
  elim (H8 s3).
  apply first_in.
  rewrite <- H9; auto.
  
  left; auto.
  
  elim H4.
  intros; apply short.
  elim H5; intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply
   (inc_dec_in_post (Collect_message Message (bm c) s1 owner) s5 s4 owner s3).
  rewrite collect_elsewhere.
  auto.
  
  left.
  unfold not in |- *; intro.
  rewrite H8 in a.
  rewrite a in H6; discriminate.
  
  intro; discriminate.
  
  intros.
  apply long with (s1 := s0).
  auto.
  
  elim H7.
  intros; apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply
   (inc_dec_in_post (Collect_message Message (bm c) s1 owner) s6 s5 owner s3).
  rewrite collect_elsewhere; auto.
  left; unfold not in |- *; intro.
  rewrite H10 in a.
  rewrite a in H8; discriminate.
  
  intro; discriminate.
  
  elim H1.
  intros.
  apply indirect_son1_intro.
  auto.
  
  generalize H3; simpl in |- *; auto.
  
  generalize H4; simpl in |- *.
  rewrite post_elsewhere.
  rewrite collect_elsewhere.
  auto.
  
  left.
  unfold not in |- *.
  intro.
  generalize H3; simpl in |- *.
  rewrite <- H5; rewrite a; auto with bool.
  
  left; auto.
  
  intro HA.
  
  
  elim (H0 H s).
  intros.
  decompose [and] H2.
  
  elim (decide_ancestor c x s s1).
  intro.
  elim (decide_direct_son (rec_inc_trans c s1 s3) s1).
  intro.
  split with s1.
  split.
  auto.
  
  case (eq_site_dec s1 s).
  intro.
  generalize H1.
  rewrite <- e0.
  generalize e0.
  elim a.
  intros.
  generalize H8 e0 e1.
  elim H9.
  intros.
  elim H12.
  rewrite e1; rewrite <- e2.
  auto.
  
  intro.
  elim H5.
  intuition.
  
  intro.
  generalize a e.
  elim H6.
  intros.
  apply short.
  generalize a0 e0.
  elim H7.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply inc_dec_in_post.
  cut (s4 <> s5).
  intro.
  rewrite collect_elsewhere.
  auto.
  
  left.
  apply (not_reflexive c).
  auto.
  
  apply inc_dec_in.
  auto.
  
  apply (not_reflexive c).
  auto.
  
  apply inc_dec_in.
  auto.
  
  auto.
  
  intro; discriminate.
  
  intros.
  apply (long (rec_inc_trans c s2 s3) s2 s0 s4).
  apply H8.
  auto.
  
  auto.
  
  generalize H7 a0 e0.
  elim H9.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply inc_dec_in_post.
  rewrite collect_elsewhere.
  auto.
  
  left.
  generalize (parent_intro c s5 s6 H10 H11).
  intro.
  generalize (long c s2 s5 s6 H12 H13).
  intro.
  apply ancestor_not_reflexive with (c := c).
  auto.
  
  auto.
  
  intro; discriminate.
  
  intro.
  split with x.
  
  elim (direct_or_indirect_son1 (rec_inc_trans c s1 s3) s1).
  intro; elim b; auto.
  
  intro.
  split.
  generalize b; elim H3.
  intro s0; intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *.
  auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  case (eq_site_dec s1 s0).
  intro.
  intro.
  rewrite e0.
  unfold not in |- *; intro.
  generalize (H8 s2).
  intro.
  elim H10.
  apply (inc_dec_in_collect2 (bm c) (inc_dec s3) s0 s1 owner s2).
  auto.
  
  rewrite e0; auto.
  
  intro.
  rewrite collect_elsewhere.
  auto.
  
  left; auto.
  
  left; auto.
  
  generalize b0; elim H4.
  intros.
  apply short.
  generalize b1; elim H6.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  case (eq_queue_dec owner s5 s3 owner).
  intro.
  case (eq_site_dec s1 s5).
  intro.
  decompose [and] a.
  generalize e.
  rewrite e0; rewrite <- H9.
  rewrite empty_q_to_me.
  simpl in |- *.
  intro; discriminate.
  
  auto.
  
  intro.
  decompose [and] a.
  rewrite H10; rewrite H9.
  rewrite post_here.
  rewrite collect_elsewhere.
  simpl in |- *.
  generalize H8; rewrite H9; auto.
  
  left; auto.
  
  intro.
  rewrite post_elsewhere.
  case (eq_site_dec s1 s5).
  intro.
  generalize e0.
  generalize o.
  elim b2.
  simpl in |- *.
  intros.
  generalize H11.
  rewrite post_elsewhere.
  rewrite e0.
  rewrite e1.
  auto.
  generalize e.
  rewrite e0.
  generalize H8.
  rewrite collect_here.
  elim (bm c s5 owner).
  simpl in |- *.
  intuition.
  
  intros d q.
  case q.
  simpl in |- *.
  intros.
  elim H14.
  intro.
  unfold not in |- *; intro; contradiction.
  
  case d.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  auto.
  
  simpl in |- *; auto.
  
  auto.
  
  intro; rewrite collect_elsewhere.
  auto.
  
  left; auto.
  
  auto.
  
  intros.
  apply long with (s1 := s0).
  generalize (H7 b1); intro.
  auto.
  
  elim H8.
  intros.
  apply parent_intro.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  apply
   (inc_dec_in_post (Collect_message Message (bm c) s1 owner) s6 s5 owner s3).
  case (eq_site_dec s1 s6).
  intro.
  rewrite e0; rewrite collect_here.
  generalize H10.
  generalize e0; elim b1.
  simpl in |- *.
  intros.
  generalize H13; rewrite post_elsewhere.
  rewrite e1.
  rewrite e0.
  rewrite collect_here.
  generalize H14.
  elim (bm c s6 owner).
  simpl in |- *; intuition.
  
  intros d q.
  case q.
  simpl in |- *.
  intros.
  elim H17; intro; unfold not in |- *; intro; contradiction.
  
  case d.
  simpl in |- *; auto.
  
  simpl in |- *; auto.
  
  simpl in |- *; auto.
  
  left; auto.
  
  intro.
  rewrite collect_elsewhere; auto.
  
  intro; discriminate.
  
  unfold not in |- *; intro.
  generalize e; rewrite H6.
  rewrite empty_q_to_me.
  simpl in |- *; discriminate.
  
  auto.
  
  
  simpl in |- *.
  elim H5.
  intro.
  rewrite H6.
  apply ancestor_rt2 with (s1 := x).
  auto.
  
  auto.
  
  intro.
  apply ancestor_rt with (s2 := s).
  auto.
  
  auto.
  
  unfold not in |- *; intro.
  generalize e; rewrite H6.
  rewrite empty_q_to_me.
  simpl in |- *; discriminate.
  
  auto.
  
  intro.
  split with x.
  split.
  generalize H4 H5.
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  rewrite collect_elsewhere.
  auto.
  
  left.
  unfold not in |- *; intro.
  generalize (not_inc_dec_in (bm c s0 owner) H8).
  intro.
  generalize e; rewrite H11.
  intro.
  elim (H12 s3).
  apply first_in.
  auto.
  
  left; auto.
  
  (* ancestor *)
  
  generalize H5.
  elim H4.
  intros.
  apply short.
  generalize H7; elim H6.
  intros.
  apply parent_intro.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  apply
   (inc_dec_in_post (Collect_message Message (bm c) s1 owner) s5 s4 owner s3).
  rewrite collect_elsewhere.
  auto.
  
  left.
  decompose [and] H10; auto.
  
  intro; discriminate.
  
  intros.
  apply long with (s1 := s0).
  apply H7.
  
  split.
  decompose [and] H9.
  unfold not in |- *; intro.
  elim H11.
  rewrite H12; apply short; auto.
  
  decompose [and] H9.
  unfold not in |- *; intro.
  elim H11.
  apply long with (s1 := s0).
  auto.
  
  auto.
  generalize H9; elim H8.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply
   (inc_dec_in_post (Collect_message Message (bm c) s1 owner) s6 s5 owner s3).
  rewrite collect_elsewhere; auto.
  left; decompose [and] H12; auto.
  
  intro; discriminate.
  
  auto.
  
  auto.
  
  apply indirect_son1_intro.
  unfold not in |- *; intro.
  generalize e; rewrite H5.
  rewrite empty_q_to_me.
  simpl in |- *; discriminate.
  
  auto.
  
  
  
  auto.
  
  unfold not in |- *; intro.
  generalize (not_inc_dec_in (bm c s1 owner) H5).
  intro.
  generalize (H6 s3).
  elim (H6 s3).
  apply first_in.
  auto.
  
  
  (* from here *)
  
  elim (decide_direct_son c s).
  elim H1.
  intros.
  generalize H2 H3 H4; elim a.
  intros.
  unfold not in |- *.
  elim H10.
  simpl in |- *.
  rewrite post_elsewhere.
  rewrite collect_elsewhere.
  auto.
  
  left; unfold not in |- *.
  intro.
  generalize e.
  rewrite H11.
  intro.
  generalize (not_inc_dec_in (bm c s2 owner) H7).
  intro.
  elim (H12 s3).
  apply first_in.
  auto.
  
  left; auto.
  
  intro.
  elim (direct_or_indirect_son1 c s).
  intro; elim b; auto.
  
  auto.
  
  elim H1.
  auto.
  
  elim H1; auto.
  
  elim H1; auto.
  
  
  
  (* 4 *)
  
  simpl in |- *.
  intros s1 s2 e e0 H H0 Hnext; intros.
  elim (H0 H s).
  intros.
  split with x.
  decompose [and] H2.
  split.
  elim H3; intros; apply direct_son_intro; auto.
  simpl in |- *; auto.
  intros.
  apply inc_dec_not_in_post.
  apply inc_dec_not_in_collect with (m := copy).
  auto.
  
  auto.
  
  discriminate.
  
  intro.
  discriminate.
  
  elim H4.
  intros.
  apply short.
  elim H5.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply inc_dec_in_post.
  apply inc_dec_in_collect with (m := copy).
  auto.
  
  auto.
  
  discriminate.
  
  intro.
  discriminate.
  
  intros.
  apply long with (s1 := s3).
  auto.
  
  elim H7.
  intros.
  apply parent_intro.
  simpl in |- *; auto.
  
  simpl in |- *.
  apply inc_dec_in_post.
  apply (inc_dec_in_collect (bm c) s6 s1 s2 s5 copy).
  auto.
  
  auto.
  
  discriminate.
  
  intro; discriminate.
  
  
  elim H1.
  intros.
  apply indirect_son1_intro.
  auto.
  generalize H3.
  simpl in |- *.
  auto.
  generalize H4.
  simpl in |- *.
  intro.
  unfold not in |- *.
  intro.
  elim H5.
  intro.
  generalize (H6 s3).
  intro.
  unfold not in |- *.
  intro.
  elim H7.
  generalize H8.
  case (eq_queue_dec s2 s0 s1 owner).
  intro.
  decompose [and] a.
  rewrite H9; rewrite H10.
  rewrite post_here.
  simpl in |- *.
  rewrite collect_elsewhere.
  auto.
  right; auto.
  intro.
  rewrite post_elsewhere.
  case (eq_queue_dec s1 s0 s2 owner).
  intro.
  decompose [and] a.
  rewrite H9; rewrite H10.
  generalize (inc_dec_in_collect2 (bm c) copy s0 s0 owner s3).
  intro.
  intro.
  apply H11.
  rewrite <- H9; rewrite <- H10.
  auto.
  auto.
  intro.
  rewrite collect_elsewhere.
  auto.
  auto.
  auto.
  
  
  (* 5 *)
  
  simpl in |- *.
  intros s2 e e0 H H0 Hnext; intros.
  elim (direct_or_indirect_son1 (rec_copy2_trans c s2) s2).
  intro.
  elim (H0 H s).
  intros.
  split with x.
  decompose [and] H2.
  split.
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro.
  generalize e.
  rewrite H8; rewrite H6; auto with bool.
  
  simpl in |- *.
  rewrite collect_elsewhere; auto.
  
  elim H4.
  intros.
  apply short.
  elim H5; intros.
  apply parent_intro.
  simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro.
  generalize e; rewrite H8; rewrite H6; auto with bool.
  
  simpl in |- *.
  case (eq_queue_dec owner s4 s2 owner).
  intro; decompose [and] a0.
  rewrite H9 in e.
  rewrite <- H8 in H6.
  rewrite H6 in e; discriminate.
  
  intro; rewrite collect_elsewhere; auto.
  
  intros.
  apply long with (s1 := s1).
  auto.
  
  elim H7.
  intros.
  apply parent_intro.
  simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro.
  generalize e; rewrite H10; rewrite H8; discriminate.
  
  simpl in |- *.
  case (eq_queue_dec owner s5 s2 owner); intro.
  decompose [and] a0.
  rewrite H11 in e; rewrite <- H10 in H8; rewrite e in H8; discriminate.
  
  rewrite collect_elsewhere; auto.
  
  cut (s2 <> s).
  elim H1.
  intros.
  apply indirect_son1_intro.
  auto.
  
  generalize H3; simpl in |- *; unfold Set_rec_table in |- *;
   rewrite other_site; auto.
  
  generalize H4; simpl in |- *.
  rewrite collect_elsewhere; auto.
  
  unfold not in |- *; intro.
  rewrite H2 in H1.
  generalize H2 a; elim H1.
  intros.
  generalize H6 H5; elim a0; intros.
  elim H11.
  rewrite <- H10.
  rewrite <- H2.
  auto.
  
  
  intro.
  case (eq_site_dec s2 s).
  intro.
  
  elim (decide_inc_dec_in_queue (rec_copy2_trans c s2) s2).
  intro.
  elim a.
  intros.
  
  elim (decide_direct_son c x).
  intro.
  split with x.
  split.
  cut (s2 <> x).
  elim a0.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite collect_elsewhere; auto.
  
  unfold not in |- *; intro.
  rewrite <- H2 in a0.
  generalize e; elim a0; intros.
  rewrite e2 in H4; discriminate.
  
  apply short.
  rewrite <- e1.
  apply parent_intro.
  simpl in |- *.
  unfold Set_rec_table in |- *; rewrite that_site.
  auto.
  
  auto.
  
  intro HA.
  
  elim (H0 H x).
  intros.
  decompose [and] H2.
  split with x0.
  split.
  cut (s2 <> x0).
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite collect_elsewhere; auto.
  
  elim H3.
  intros.
  unfold not in |- *; intro.
  generalize e; rewrite H8; rewrite H6; auto with bool.
  
  apply long with (s1 := x).
  elim H4.
  intros.
  apply short.
  elim H5.
  intros.
  apply parent_intro.
  simpl in |- *.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro.
  generalize e; rewrite H8; rewrite H6; auto with bool.
  
  simpl in |- *.
  rewrite collect_elsewhere; auto.
  right; unfold not in |- *; intro; generalize e0.
  rewrite H8; rewrite empty_q_to_me.
  simpl in |- *; discriminate.
  
  auto.
  
  intros.
  apply long with (s1 := s1).
  auto.
  
  elim H7.
  intros; apply parent_intro.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro; generalize e.
  rewrite H10; rewrite H8; auto with bool.
  
  simpl in |- *; rewrite collect_elsewhere; auto.
  right; unfold not in |- *; intro; generalize e0.
  rewrite H10; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  apply parent_intro.
  rewrite <- e1; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite that_site; auto.
  
  rewrite <- e1.
  auto.
  
  cut (inc_dec_in_queue x (bm c s2 owner)).
  intro.
  generalize (inc_dec_in x (bm c s2 owner) H2).
  intro.
  generalize (not_owner_inc3 c s2 owner H x H3); intro.
  generalize (positive_st c x s2 H4 H H3); intro.
  generalize (st_rt c x H H4 H5); intro.
  apply indirect_son1_intro.
  auto.
  
  auto.
  
  elim (direct_or_indirect_son1 c x H4 H6).
  intro; elim HA; auto.
  
  intro.
  elim b0.
  auto.
  
  generalize p; simpl in |- *.
  rewrite collect_elsewhere; auto.
  left; unfold not in |- *; intro.
  generalize e0; rewrite H2; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  cut (inc_dec_in_queue x (bm c s2 owner)).
  intro.
  generalize (inc_dec_in x (bm c s2 owner) H2).
  intro.
  generalize (not_owner_inc3 c s2 owner H x H3); intro.
  auto.
  
  generalize p; simpl in |- *.
  rewrite collect_elsewhere; auto.
  left; unfold not in |- *; intro.
  generalize e0; rewrite H2; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  generalize e1; elim b; intros.
  elim H4.
  rewrite e1; rewrite <- e2; auto.
  
  intro.
  elim (H0 H s).
  intros.
  split with x.
  decompose [and] H2.
  split.
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro; generalize e.
  rewrite H8; rewrite H6; auto with bool.
  
  simpl in |- *.
  rewrite collect_elsewhere; auto.
  
  generalize n; elim H4.
  intros.
  apply short.
  generalize n0; elim H5; intros; apply parent_intro.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite collect_elsewhere; auto.
  right; unfold not in |- *; intro.
  generalize e0; rewrite H8; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.

  intros.
  apply long with (s1 := s1).
  apply H6.
  generalize e; elim H5; intros.
  generalize e1; elim H8; intros.
  unfold not in |- *; intro.
  generalize e2; rewrite H11; rewrite H9; auto with bool.
  
  generalize e1; elim H10.
  intros.
  unfold not in |- *.
  intro; generalize e2.
  rewrite H13; rewrite H11; auto with bool.
  
  generalize n0; elim H7; intros.
  apply parent_intro.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *; rewrite collect_elsewhere; auto.
  right; unfold not in |- *; intro.
  generalize e0; rewrite H10; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  
  generalize n; elim H1.
  intros.
  apply indirect_son1_intro.
  auto.
  
  generalize H3; simpl in |- *; unfold Set_rec_table in |- *;
   rewrite other_site; auto.
  
  generalize H4; simpl in |- *; rewrite collect_elsewhere.
  auto.
  
  right; unfold not in |- *; intro; generalize e0.
  rewrite H5; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  unfold not in |- *; intro; generalize e0.
  rewrite H2; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite that_site; auto.
  
  (* 6 *)
  
  
  
  simpl in |- *.
(*petit pb :       n0*)
  intros s1 s2 e n e0 H H0 Hnext; intros s H1.
(*end petit pb*)
  case (eq_site_dec s2 s).
  intro.
  elim (decide_direct_son c s1 n).
  intro.
  split with s1.
  split.
  generalize e0; elim a.
  intros.
  apply direct_son_intro.
  auto.
(*
Simpl.
Unfold Set_rec_table.
Rewrite other_site.
Auto.
*)
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site;
   auto with bool.
  unfold not in |- *; intro; generalize e2.
  rewrite H5; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  intro.
  case (eq_site_dec s2 owner).
  intro.
  rewrite e3; rewrite collect_here.
  apply inc_dec_not_in_first_out with (m := copy).
  rewrite <- e3; auto.
  
  discriminate.
  
  auto.
  
  intro; rewrite collect_elsewhere; auto.
  
  left; unfold not in |- *; intro; generalize e2.
  rewrite H5; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  apply short.
  apply parent_intro.
  rewrite <- e1; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite that_site; auto.
  
  simpl in |- *.
  rewrite e1; rewrite post_here; simpl in |- *.
  case (eq_site_dec s1 s1).
  auto.
  
  intro.
  auto.
  
  intro.
  elim (direct_or_indirect_son1 c s1 n).
  intro; elim b; auto.
  
  intro.
  elim (H0 H s1 b0).
  intros.
  split with x.
  decompose [and] H2.
  split.
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro; generalize e.
  rewrite H8; rewrite H6; auto with bool.
  
  simpl in |- *.
  rewrite post_elsewhere.
  case (eq_queue_dec s1 s0 s2 owner).
  intro; decompose [and] a.
  rewrite H8; rewrite H9; rewrite collect_here.
  intro.
  apply inc_dec_not_in_first_out with (m := copy).
  rewrite <- H8; rewrite <- H9; auto.
  
  discriminate.
  
  auto.
  
  intro; rewrite collect_elsewhere; auto.
  
  left; unfold not in |- *; intro; generalize e.
  rewrite H8; rewrite H6; auto with bool.
  
  apply long with (s1 := s1).
  generalize H4.
  (* I could not eliminate H5 directly cos sites were renamed
     in  (rec_copy3_trans c s1 s2) .
     So I generalize the term as follows.  *)
  cut
   (forall sa sb : Site,
    ancestor c sa sb -> sb <> s2 -> ancestor (rec_copy3_trans c s1 s2) sa sb).
  intros.
  apply H5.
  auto.
  
  elim b0.
  intros.
  unfold not in |- *; intro; generalize e.
  rewrite <- H10; rewrite H8; auto with bool.
  
  intros.
  generalize H6.
  elim H5.
  intros; apply short.
  generalize H8; elim H7; intros; apply parent_intro.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  apply (inc_dec_in_collect (bm c) s5 s1 s2 s4 copy).
  auto.
  
  auto.
  
  discriminate.
  
  left; auto.
  
  intros.
  apply long with (s1 := s3).
  apply H8.
  elim H7.
  intros.
  elim H11.
  intros.
  unfold not in |- *; intro; generalize H12.
  rewrite H14; rewrite e; auto with bool.
  
  intros.
  elim H13; intros.
  unfold not in |- *; intro; generalize H14.
  rewrite H16; rewrite e; auto with bool.
  
  generalize H10.
  elim H9.
  intros.
  apply parent_intro.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  apply (inc_dec_in_collect (bm c) s6 s1 s2 s5 copy).
  auto.
  
  auto.
  
  discriminate.
  
  left; auto.
  apply parent_intro.
  simpl in |- *.
  rewrite e1; unfold Set_rec_table in |- *; rewrite that_site; auto.
  
  simpl in |- *.
  rewrite e1; rewrite post_here; simpl in |- *.
  case (eq_site_dec s1 s1).
  auto.
  
  auto.
  
  generalize e1; elim H1; simpl in |- *.
  intros.
  cut (inc_dec_in_queue s1 (bm (rec_copy3_trans c s1 s2) s2 owner)).
  intro.
  generalize (inc_dec_in s1 (bm (rec_copy3_trans c s1 s2) s2 owner) H5).
  intro.
  cut (s1 <> owner).
  intro.
  generalize (positive_st (rec_copy3_trans c s1 s2) s1 s2 H7 Hnext H6).
  intro.
  generalize (st_rt (rec_copy3_trans c s1 s2) s1 Hnext H7 H8).
  simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro; generalize e0.
  rewrite H9; rewrite empty_q_to_me; simpl in |- *.
  discriminate.
  
  auto.
  
  auto.
  
  simpl in |- *.
  rewrite post_here; simpl in |- *; auto.
  case (eq_site_dec s1 s1).
  auto.
  
  auto.
  
     (* ~s2=s *)
  
  intro.
  elim (H0 H s).
  intros.
  decompose [and] H2.
  split with x.
  split.
  elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  unfold not in |- *; intro; generalize e.
  rewrite H8; rewrite H6; auto with bool.
  
  simpl in |- *.
  rewrite post_elsewhere.
  intro.
  apply inc_dec_not_in_collect with (m := copy).
  auto.
  
  auto.
  
  discriminate.
  
  left.
  unfold not in |- *; intro; generalize e.
  rewrite H8; rewrite H6; auto with bool.
  
  generalize n0.
  elim H4.
  intros.
  apply short.
  generalize n1; elim H5; intros.
  apply parent_intro.

  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.

  simpl in |- *.
  rewrite post_elsewhere.
  apply inc_dec_in_collect with (m := copy).
  auto.
  
  auto.
  
  discriminate.
  
  left; auto.
  
  intros.
  apply long with (s1 := s3).
  apply H6.
  elim H5; intros.
  elim H8; intros.
  unfold not in |- *; intro; generalize e.
  rewrite H11; rewrite H9; auto with bool.
  
  elim H10; intros.
  unfold not in |- *; intro; generalize e.
  rewrite H13; rewrite H11; auto with bool.
  
  generalize n1; elim H7.
  intros.
  apply parent_intro.
  simpl in |- *; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite post_elsewhere.
  apply (inc_dec_in_collect (bm c) s6 s1 s2 s5 copy).
  auto.
  
  auto.
  
  discriminate.
  
  left; auto.
  
  generalize n0; elim H1; intros.
  apply indirect_son1_intro.
  auto.
  
  generalize H3; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  unfold not in |- *; intro.
  elim H4; simpl in |- *.
  intro; rewrite post_elsewhere.
  apply inc_dec_not_in_collect with (m := copy).
  auto.

  exact (H5 s3).

  discriminate.
  
  left; auto.
  
  (* 7 *)
  
  simpl in |- *.
  intros s e e0 n H H0 Hnext; intros s0 H1.
  elim (H0 H s0).
  intros.
  decompose [and] H2.
  split with x.
  split.
  cut (s <> x).
  intro.
  generalize H5; elim H3.
  intros.
  apply direct_son_intro.
  auto.
  
  simpl in |- *.
  unfold Reset_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  intro.
  apply inc_dec_not_in_post.
  auto.
  
  intro; discriminate.
  
  generalize (ancestor_has_positive_st c H x s0 H4); intro.
  unfold not in |- *; intro.
  generalize H5; rewrite <- H6; rewrite e.
  intro.
  omega.
  
  generalize H1.
  elim H4.
  intros.
  apply short.
  generalize H6; elim H5; intros.
  cut (s4 <> s).
  intro; apply parent_intro.
  simpl in |- *; unfold Reset_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite post_elsewhere; auto.
  
  elim H9.
  simpl in |- *.
  intros.
  unfold not in |- *; intro.
  rewrite H13 in H11.

  generalize H11; unfold Reset_rec_table in |- *; rewrite that_site;
   auto with bool.
  
  intros.
  apply long with (s1 := s1).
  apply H6.
  generalize H7; elim H5.
  intros.
  apply indirect_son1_intro.
  elim H10.
  intros.
  apply (not_owner_inc3 c s7 owner H).
  apply inc_dec_in.
  auto.
  
  auto.
  
  simpl in |- *; unfold Reset_rec_table in |- *; rewrite other_site; auto.
  elim H9; auto.
  
  generalize (short c s5 s3 H10); intro.
  generalize (ancestor_has_positive_st c H s5 s3 H11); intro.
  unfold not in |- *; intro; generalize e.
  rewrite H13; intro.
  rewrite e1 in H12; omega.
  
  simpl in |- *.
  elim H9; intros.
  case (eq_site_dec s s7).
  intro.
  rewrite e1; rewrite post_here; simpl in |- *; auto.
  unfold not in |- *; intro.
  apply (H13 s6).
  auto.
  
  intro; rewrite post_elsewhere.
  unfold not in |- *; intro.
  apply (H13 s6); auto.
  
  left; auto.
  
  intros.
  apply indirect_son1_intro.
  
  elim H12.
  intros.
  apply (not_owner_inc3 c s8 owner H).
  apply inc_dec_in.
  auto.
  
  auto.
  
  simpl in |- *; unfold Reset_rec_table in |- *; rewrite other_site; auto.
  elim H11; auto.
  
  generalize (short c s6 s3 H12); intro.
  generalize (ancestor_has_positive_st c H s6 s3 H13); intro.
  unfold not in |- *; intro.
  rewrite H15 in e; rewrite e in H14; omega.
  
  simpl in |- *.
  elim H11; intros.
  unfold not in |- *; intros.
  apply (H15 s7).
  apply inc_dec_in_post.
  auto.
  
  intro; discriminate.
  
  generalize H8; elim H7.
  intros.
  cut (s5 <> s).
  intro.
  apply parent_intro.
  simpl in |- *; unfold Reset_rec_table in |- *; rewrite other_site; auto.
  
  simpl in |- *.
  rewrite post_elsewhere; auto.
  
  elim H11.
  intros.
  unfold not in |- *; intro.
  generalize H13; rewrite H15; simpl in |- *; unfold Reset_rec_table in |- *;
   rewrite that_site; auto with bool.
  
  generalize H1; elim H1; intros.
  apply indirect_son1_intro.
  auto.
  
  generalize H3; simpl in |- *; unfold Reset_rec_table in |- *;
   rewrite other_site; auto.
  elim H5; intros.
  unfold not in |- *; intro; generalize H7.
  rewrite H9; simpl in |- *; unfold Reset_rec_table in |- *;
   rewrite that_site; auto with bool.
  
  generalize H4; simpl in |- *.
  intro.
  unfold not in |- *; intro.
  elim H6.
  intro.
  unfold not in |- *; intro.
  apply (H7 s2).
  apply (inc_dec_in_post2 (bm c) s1 s2 s owner dec).
  auto.
  
  discriminate.
Qed.


Lemma parent_invariant :
 forall c : Config,
 legal c ->
 forall s : Site,
 indirect_son1 c s -> exists s1 : Site, direct_son c s1 /\ ancestor c s1 s.
Proof.
  intros c H.
  generalize H.
  elim H.
  simpl in |- *.
  intros.
  elim H1.
  simpl in |- *.
  intros.
  elim H4.
  intro; auto.
  unfold not in |- *; auto.

  exact parent_invariant_inductive.
Qed.


