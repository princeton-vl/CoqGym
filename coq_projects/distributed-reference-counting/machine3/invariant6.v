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


Require Export DistributedReferenceCounting.machine3.invariant0.
Require Export DistributedReferenceCounting.machine3.invariant1.
Require Export DistributedReferenceCounting.machine3.invariant2.
Require Export DistributedReferenceCounting.machine3.invariant3.
Require Export DistributedReferenceCounting.machine3.invariant4.

Unset Standard Proposition Elimination Names.

(* changes:
   only a few changes in ancestor_not_reflexive for
   transition  6 ,  where n0->n1, n1-> n2, n2-> n3.
*)




Section INVARIANT6.

Variable c0 : Config.

Fixpoint inc_dec_in_queue (s : Site) (q : queue Message) {struct q} : Prop :=
  match q with
  | empty => False
  | input (inc_dec s2) q' => if eq_site_dec s2 s then True else False
  | input _ q' => inc_dec_in_queue s q'
  end.
	
(* note that the contrary is not true ! *)

Lemma inc_dec_in :
 forall (s : Site) (q : queue Message),
 inc_dec_in_queue s q -> In_queue Message (inc_dec s) q.

Proof.
  simple induction q.
  simpl in |- *.
  auto.
  simpl in |- *.
  intro.
  intro.
  intro.
  case d.
  intuition.
  intro.
  case (eq_site_dec s0 s).
  intro.
  rewrite e.
  intuition.
  intro.
  intuition.
  intuition.
Qed.



Lemma inc_dec_queue_equal :
 forall (q : queue Message) (s1 s2 : Site),
 inc_dec_in_queue s1 q -> inc_dec_in_queue s2 q -> s1 = s2.

Proof.
  simple induction q.
  simpl in |- *.
  intuition.
  simpl in |- *.
  intros d q0 s1 s2.
  intro s0.
  case d.
  auto.
  intro.
  case (eq_site_dec s s2).
  case (eq_site_dec s s0).
  intros.
  rewrite <- e; rewrite e0.
  auto.
  intuition.
  intuition.
  auto.
Qed.




(* s1 is parent of s0 *)
Inductive parent : Site -> Site -> Prop :=
    parent_intro :
      forall s1 s0 : Site,
      rt c0 s0 = true -> inc_dec_in_queue s1 (bm c0 s0 owner) -> parent s1 s0.

(* s1 is ancestor of s0 *)
Inductive ancestor : Site -> Site -> Prop :=
  | short : forall s1 s0 : Site, parent s1 s0 -> ancestor s1 s0
  | long :
      forall s2 s1 s0 : Site,
      ancestor s2 s1 -> parent s1 s0 -> ancestor s2 s0.


Lemma decide_rt : forall s : Site, {rt c0 s = false} + {rt c0 s = true}.
Proof.
  intros.
  case (rt c0 s).
  auto.
  auto.
Qed.

Lemma decide_inc_dec_in_queue :
 forall s : Site,
 {s1 : Site | inc_dec_in_queue s1 (bm c0 s owner)} +
 {(forall s1 : Site, ~ inc_dec_in_queue s1 (bm c0 s owner))}.
Proof.
  intros.
  elim (bm c0 s owner).
  simpl in |- *.
  intuition.
  
  intros.
  case d.
  simpl in |- *.
  auto.
  
  simpl in |- *.
  intros.
  left.
  split with s0.
  case (eq_site_dec s0 s0).
  auto.
  intro; elim n; auto.
  simpl in |- *; auto.
Qed.



Lemma decide_parent : forall s1 s3 : Site, {parent s1 s3} + {~ parent s1 s3}.

Proof.
  intros.
  elim (decide_rt s3).
  intro.
  right.
  unfold not in |- *.
  intro.
  generalize a.
  elim H.
  intros.
  rewrite H0 in a0.
  discriminate.
  
  intro.
  elim (decide_inc_dec_in_queue s3).
  intros.
  elim a.
  intros.
  case (eq_site_dec x s1).
  intro.
  left.
  apply parent_intro.
  auto.
  
  rewrite <- e.
  auto.
  
  intro.
  right.
  unfold not in |- *.
  intro.
  generalize p; generalize n.
  elim H.
  intros.
  elim n0.
  apply inc_dec_queue_equal with (q := bm c0 s2 owner).
  auto.
  
  auto.
  
  intros.
  right.
  unfold not in |- *.
  intro.
  generalize b0.
  elim H.
  intros.
  generalize (b1 s0).
  intro.
  elim H2; auto.
Qed.

Inductive direct_son : Site -> Prop :=
    direct_son_intro :
      forall s : Site,
      s <> owner ->
      rt c0 s = true ->
      (forall s1 : Site, ~ inc_dec_in_queue s1 (bm c0 s owner)) ->
      direct_son s.




Inductive indirect_son1 : Site -> Prop :=
    indirect_son1_intro :
      forall s : Site,
      s <> owner ->
      rt c0 s = true ->
      ~ (forall s1 : Site, ~ inc_dec_in_queue s1 (bm c0 s owner)) ->
      indirect_son1 s.


(*  {s1:Site | (inc_dec_in_queue s1 (bm c0 s owner))}  *)

Inductive indirect_son2 : Site -> Prop :=
    indirect_son2_intro :
      forall s s1 : Site,
      s <> owner /\ rt c0 s = true /\ direct_son s1 /\ ancestor s1 s ->
      indirect_son2 s.

(* by specifying the lemma as follows, I don't need to
   know that there is no cycle in the relation *)

Lemma decide_direct_son :
 forall s1 : Site, s1 <> owner -> {direct_son s1} + {~ direct_son s1}.
Proof.
  intros.
  elim (decide_rt s1).
  intros.
  right.
  unfold not in |- *.
  intro.
  generalize a.
  elim H0.
  intros.
  rewrite H2 in a0.
  discriminate.
  
  intro.
  elim (decide_inc_dec_in_queue s1).
  intro.
  right.
  unfold not in |- *.
  intro.
  generalize a.
  elim H0.
  intros.
  elim a0.
  auto.
  
  intro.
  left.
  apply direct_son_intro.
  auto.
  auto.
  auto.
Qed.



Lemma direct_or_indirect_son1 :
 forall s : Site,
 s <> owner -> rt c0 s = true -> {direct_son s} + {indirect_son1 s}.

Proof.
  intros.
  elim (decide_inc_dec_in_queue s).
  intro.
  right.
  apply (indirect_son1_intro s).
  auto.
  auto.
  unfold not in |- *; intros.
  elim a.
  auto.
  intros; left.
  apply (direct_son_intro s).
  auto.
  auto.
  auto.
Qed.


Lemma disjoint_case_for_site :
 forall s : Site,
 {s = owner} + {rt c0 s = false} + {direct_son s} + {indirect_son1 s}.
Proof.
  intro.
  case (eq_site_dec s owner).
  intro.
  auto.
  intro.
  generalize (direct_or_indirect_son1 s).
  intro.
  elim (decide_rt s).
  intro.
  auto.
  intro.
  auto.
  elim H.
  auto.
  auto.
  auto.
  auto.
Qed.


Lemma ancestor_transitive :
 forall s1 s2 s3 : Site, ancestor s1 s2 -> ancestor s2 s3 -> ancestor s1 s3.
Proof.
  intros s1 s2 s3 H.
  intro.
  generalize H.
  elim H0.
  intros.
  apply long with (s1 := s0).
  auto.
  auto.
  intros.
  apply long with (s1 := s4).
  auto.
  auto.
Qed.


Lemma aux :
 forall s0 s1 s2 : Site,
 parent s0 s2 -> direct_son s0 -> ancestor s1 s2 -> s1 = s0.
Proof.
   intros.
  generalize H H0.
  elim H1.
  intros.
  apply inc_dec_queue_equal with (q := bm c0 s4 owner).
  elim H2; auto.
  
  elim H3; auto.
  
  intros.
  cut (s0 = s4).
  intro.
  rewrite <- H7 in H2.
  generalize H2.
  elim H6.
  intros.
  generalize H10.
  elim H11.
  intros.
  generalize H13.
  elim H12.
  intros.
  elim (H16 s8).
  auto.
  
  intros.
  generalize H15.
  elim H14.
  intros.
  elim (H18 s9).
  auto.
  
  apply inc_dec_queue_equal with (q := bm c0 s5 owner).
  elim H5; auto.
  
  elim H4; auto.
Qed.



Lemma decide_ancestor :
 forall x s s1 : Site,
 direct_son x ->
 ancestor x s ->
 indirect_son1 s1 -> (s1 = s \/ ancestor s1 s) \/ s1 <> s /\ ~ ancestor s1 s.
Proof.
  intros.
  generalize H H1.
  elim H0.
  intros.
  case (eq_site_dec s1 s2).
  intro.
  left; left; auto.
  
  intro.
  case (eq_site_dec s0 s1).
  intro.
  generalize H3.
  rewrite e.
  elim H4.
  intros.
  intros.
  generalize H7.
  elim H8.
  intros.
  elim H12.
  auto.
  
  intro.
  right.
  split; auto.
  unfold not in |- *.
  intro.
  generalize (aux s0 s1 s2 H2 H3 H5).
  intro; elim n0; auto.
  
  intros.
  generalize (H3 H5 H1).
  intro.
  elim H7.
  intro.
  case (eq_site_dec s1 s3).
  intro.
  left; left; auto.
  
  intro.
  left; right.
  case (eq_site_dec s1 s0).
  intro.
  apply short.
  rewrite e; auto.
  
  intro.
  apply long with (s1 := s0).
  elim H8.
  intro; elim n0; auto.
  
  auto.
  
  auto.
  
  intro.
  case (eq_site_dec s1 s3).
  intro.
  left; left; auto.
  
  intro.
  right.
  split; auto.
  unfold not in |- *.
  intro.
  decompose [and] H8.
  generalize H4 H11 H10 n.
  elim H9.
  intros.
  elim H15.
  apply inc_dec_queue_equal with (q := bm c0 s5 owner).
  elim H12; auto.
  
  elim H13; auto.
  
  intros.
  cut (s0 = s5).
  intro.
  rewrite H18 in H16.
  elim H16; auto.
  
  apply inc_dec_queue_equal with (q := bm c0 s6 owner).
  elim H15; auto.
  
  elim H14; auto.
Qed.

End INVARIANT6.

Section INVARIANT6_bis.


Lemma inc_dec_in_post :
 forall (b : Bag_of_message) (s0 s1 s2 s3 : Site) (m : Message),
 inc_dec_in_queue s1 (b s0 owner) ->
 (forall s4 : Site, m <> inc_dec s4) ->
 inc_dec_in_queue s1 (Post_message Message m b s2 s3 s0 owner).
Proof.
   intros.
   case (eq_queue_dec s2 s0 s3 owner).
   intros.
   decompose [and] a.
   rewrite H1; rewrite H2.
   rewrite post_here.
   generalize H0.
   case m.
   simpl in |- *; auto.
   
   intro.
   intro.
   generalize (H3 s).
   intro.
   elim H4; auto.
   
   simpl in |- *; auto.
   
   intro; rewrite post_elsewhere; auto.
Qed.

Lemma inc_dec_in_post2 :
 forall (b : Bag_of_message) (s0 s1 s2 s3 : Site) (m : Message),
 inc_dec_in_queue s1 (Post_message Message m b s2 s3 s0 owner) ->
 m <> inc_dec s1 -> inc_dec_in_queue s1 (b s0 owner).
Proof.
  intros.
  generalize H.
  case (eq_queue_dec s2 s0 s3 owner).
  intros.
  decompose [and] a.
  generalize H1.
  rewrite H2; rewrite H3.
  rewrite post_here.
  generalize H0.
  elim m.
  simpl in |- *; auto.
  intro; intro.
  simpl in |- *.
  case (eq_site_dec s s1).
  intro; elim H4.
  rewrite e; auto.
  intuition.
  simpl in |- *; auto.
  intro.
  rewrite post_elsewhere.
  auto.
  auto.
Qed.


(* these two lemmas are just negations of the previous ones *)


Lemma inc_dec_not_in_post :
 forall (b : Bag_of_message) (s0 s1 s2 s3 : Site) (m : Message),
 ~ inc_dec_in_queue s1 (b s0 owner) ->
 (forall s4 : Site, m <> inc_dec s4) ->
 ~ inc_dec_in_queue s1 (Post_message Message m b s2 s3 s0 owner).
Proof.
  intros.
  unfold not in |- *.
  intro.
  elim H.
  apply (inc_dec_in_post2 b s0 s1 s2 s3 m).
  auto.
  auto.
Qed.


Lemma inc_dec_not_in_post2 :
 forall (b : Bag_of_message) (s0 s1 s2 s3 : Site) (m : Message),
 (forall s4 : Site, m <> inc_dec s4) ->
 ~ inc_dec_in_queue s1 (Post_message Message m b s2 s3 s0 owner) ->
 ~ inc_dec_in_queue s1 (b s0 owner).
Proof.
  intros.
  unfold not in |- *.
  intro.
  elim H0.
  apply inc_dec_in_post.
  auto.
  auto.
Qed.

Lemma inc_dec_not_in_first_out :
 forall (q : queue Message) (m : Message) (s3 : Site),
 first Message q = value Message m ->
 m <> inc_dec s3 ->
 ~ inc_dec_in_queue s3 q -> ~ inc_dec_in_queue s3 (first_out Message q).
Proof.
  simple induction q.
  simpl in |- *.
  auto.
  
  intros d q0.
  case q0.
  intro.
  intros m s3.
  simpl in |- *.
  intros.
  intuition.
  
  intros m q1 H m0 s3 H0 H1.
  case d.
  generalize (H m0 s3).
  simpl in |- *.
  auto.
  
  intro.
  case (eq_site_dec s3 s).
  intro.
  rewrite e.
  simpl in |- *.
  case (eq_site_dec s s).
  auto.
  
  intro.
  elim n; auto.
  
  intro.
  simpl in |- *.
  case (eq_site_dec s s3).
  auto.
  
  intro.
  generalize (H m0 s3).
  simpl in |- *.
  auto.
  
  generalize (H m0 s3).
  simpl in |- *.
  auto.
Qed.

Lemma inc_dec_in_first_out :
 forall (q : queue Message) (m : Message) (s3 : Site),
 first Message q = value Message m ->
 m <> inc_dec s3 ->
 inc_dec_in_queue s3 q -> inc_dec_in_queue s3 (first_out Message q).
Proof.
  simple induction q.
  simpl in |- *.
  auto.
  
  intros d q0.
  case q0.
  intro.
  intros m s3.
  simpl in |- *.
  case d.
  auto.
  
  intro.
  case (eq_site_dec s s3).
  intros.
  elim H1.
  generalize H0.
  auto.
  rewrite e.
  auto.
  generalize (inc_dec s3).
  intro.
  auto.
  intro.
  symmetry  in |- *.
  injection H3.
  auto.
  
  auto.
  
  intros.
  contradiction.
  
  intros m q1 H m0 s3 H0 H1.
  case d.
  generalize (H m0 s3).
  simpl in |- *.
  auto.
  
  intro.
  case (eq_site_dec s3 s).
  intro.
  rewrite e.
  simpl in |- *.
  case (eq_site_dec s s).
  auto.
  
  intro.
  elim n; auto.
  
  intro.
  simpl in |- *.
  case (eq_site_dec s s3).
  auto.
  
  intro.
  generalize (H m0 s3).
  simpl in |- *.
  auto.
  
  generalize (H m0 s3).
  simpl in |- *.
  auto.
Qed.



Lemma inc_dec_not_in_collect :
 forall (b : Bag_of_message) (m : Message) (s0 s1 s2 s3 : Site),
 first Message (b s1 s2) = value Message m ->
 ~ inc_dec_in_queue s3 (b s0 owner) ->
 m <> inc_dec s3 ->
 ~ inc_dec_in_queue s3 (Collect_message Message b s1 s2 s0 owner).
Proof.
  intros.
  case (eq_queue_dec s1 s0 s2 owner).
  intros.
  decompose [and] a.
  rewrite H2; rewrite H3.
  rewrite collect_here.
  apply inc_dec_not_in_first_out with (m := m).
  rewrite <- H2; rewrite <- H3; auto.
  auto.
  auto.
  intro.
  rewrite collect_elsewhere.
  auto.
  auto.
Qed.


Lemma inc_dec_in_collect :
 forall (b : Bag_of_message) (s0 s1 s2 s3 : Site) (m : Message),
 first Message (b s1 s2) = value Message m ->
 inc_dec_in_queue s3 (b s0 owner) ->
 m <> inc_dec s3 ->
 inc_dec_in_queue s3 (Collect_message Message b s1 s2 s0 owner).
Proof.
  intros.
  case (eq_queue_dec s1 s0 s2 owner).
  intros.
  decompose [and] a.
  rewrite H2; rewrite H3.
  rewrite collect_here.
  generalize (inc_dec_not_in_first_out (b s0 owner) m s3).
  intros.
  apply inc_dec_in_first_out with (m := m).
  rewrite <- H2; rewrite <- H3.
  auto.
  auto.
  auto.
  intro.
  rewrite collect_elsewhere.
  auto.
  auto.
Qed.

Lemma inc_dec_in_collect2 :
 forall (b : Bag_of_message) (m : Message) (s0 s1 s2 s3 : Site),
 first Message (b s1 s2) = value Message m ->
 inc_dec_in_queue s3 (Collect_message Message b s1 s2 s0 owner) ->
 inc_dec_in_queue s3 (b s0 owner).
Proof.
  intros b m s0 s1 s2 s3 H.
  case (eq_queue_dec s1 s0 s2 owner).
  intros.
  decompose [and] a.
  generalize H0.
  rewrite H1; rewrite H2.
  rewrite collect_here.
  elim (b s0 owner).
  simpl in |- *.
  auto.
  
  intros d q.
  case q.
  simpl in |- *.
  intuition.
  
  intro.
  case d.
  simpl in |- *.
  auto.
  
  intro.
  case (eq_site_dec s s3).
  intro.
  rewrite e.
  simpl in |- *.
  auto.
  case (eq_site_dec s3 s3).
  auto.
  
  intro.
  elim n.
  auto.
  
  intro.
  simpl in |- *.
  auto.
  
  auto.
  
  simpl in |- *.
  auto.
  
  intro.
  rewrite collect_elsewhere.
  auto.
  
  auto.
Qed.



Lemma not_inc_dec_in :
 forall q : queue Message,
 (forall s : Site, ~ inc_dec_in_queue s q) ->
 forall s : Site, ~ In_queue Message (inc_dec s) q.

Proof.
  simple induction q.
  simpl in |- *.
  auto.
  intro.
  case d.
  simpl in |- *.
  intros.
  intuition.
  discriminate.
  eauto.
  intros.
  generalize (H0 s).
  intro.
  elim H1.
  simpl in |- *.
  case (eq_site_dec s s).
  auto.
  intro; elim n; auto.
  intro; simpl in |- *.
  intros.
  intuition.
  discriminate.
  eauto.
Qed.


Lemma joining_node :
 forall (c : Config) (s2 : Site),
 legal c ->
 rt c s2 = false -> forall s3 s4 : Site, parent c s3 s4 -> s2 <> s3.
Proof.
  intros.
  unfold not in |- *.
  intro.
  rewrite H2 in H0.
  generalize H0.
  elim H1.
  intros.
  generalize (inc_dec_in s1 (bm c s0 owner) H4).
  intro.
  generalize (not_owner_inc3 c s0 owner H s1 H6).
  intro.
  generalize (positive_st c s1 s0 H7 H H6).
  intro.
  generalize (st_rt c s1 H H7 H8).
  rewrite H5.
  discriminate.
Qed.


Lemma ancestor_rt :
 forall c : Config,
 legal c -> forall s1 s2 : Site, ancestor c s1 s2 -> rt c s1 = true.
Proof.
  intros.
  elim H0.
  intros.
  elim H1.
  intros.
  generalize (inc_dec_in s4 (bm c s5 owner) H3).
  intro.
  generalize (not_owner_inc3 c s5 owner H s4 H4).
  intro.
  generalize (positive_st c s4 s5 H5 H H4).
  intro.
  generalize (st_rt c s4 H H5 H6).
  auto.
  intros.
  auto.
Qed.


Lemma ancestor_rt2 :
 forall c : Config,
 legal c -> forall s1 s2 : Site, ancestor c s1 s2 -> rt c s2 = true.
Proof.
  intros.
  elim H0.
  intros.
  elim H1.
  auto.
  intros.
  elim H3; auto.
Qed.

(* the parent of a node cannot be the which receives 
   a gp for the first time *)

Lemma parent_does_not_join :
 forall (c0 : Config) (s2 s3 s4 : Site),
 legal c0 ->
 legal (rec_copy2_trans c0 s2) ->
 parent (rec_copy2_trans c0 s2) s3 s4 ->
 rt c0 s2 = false ->
 first Message (bm c0 owner s2) = value Message copy -> s3 <> s2.
Proof.
  intros.
  elim H1.
  intros.
  generalize (inc_dec_in s1 (bm (rec_copy2_trans c0 s2) s0 owner) H5).
  intro.
  generalize (not_reflexive (rec_copy2_trans c0 s2) H0 s1 s0 H6).
  intro.
  cut (s1 <> owner).
  intro.
  generalize (positive_st (rec_copy2_trans c0 s2) s1 s0 H8 H0 H6).
  intro.
  generalize (st_rt (rec_copy2_trans c0 s2) s1 H0 H8 H9).
  intro.
  generalize H5.
  simpl in |- *.
  intro.
  generalize (inc_dec_in_collect2 (bm c0) copy s0 owner s2 s1 H3 H11).
  intro.
  generalize (inc_dec_in s1 (bm c0 s0 owner) H12).
  intro.
  generalize (positive_st c0 s1 s0 H8 H H13).
  intro.
  generalize (st_rt c0 s1 H H8 H14).
  intro.
  unfold not in |- *.
  intro.
  rewrite H16 in H15.
  rewrite H15 in H2.
  discriminate.
  
  apply (not_owner_inc3 (rec_copy2_trans c0 s2) s0 owner H0).
  auto.
Qed.

(* the ancestor of a node cannot be the which receives 
   a gp for the first time *)

Lemma ancestor_does_not_join :
 forall (c0 : Config) (s2 s3 s4 : Site),
 legal c0 ->
 legal (rec_copy2_trans c0 s2) ->
 ancestor (rec_copy2_trans c0 s2) s3 s4 ->
 rt c0 s2 = false ->
 first Message (bm c0 owner s2) = value Message copy -> s3 <> s2.
Proof.
  intros.
  elim H1.
  intros.
  apply (parent_does_not_join c0 s2 s1 s0).
  auto.
  auto.
  auto.
  auto.
  auto.
  intros.
  auto.
Qed.

Lemma parent_does_not_join2 :
 forall (c0 : Config) (s1 s2 s3 s4 : Site),
 legal c0 ->
 legal (rec_copy3_trans c0 s1 s2) ->
 parent (rec_copy3_trans c0 s1 s2) s3 s4 ->
 rt c0 s2 = false ->
 first Message (bm c0 s1 s2) = value Message copy -> s3 <> s2.
Proof.
  intros.
  elim H1.
  intros.
  generalize (inc_dec_in s0 (bm (rec_copy3_trans c0 s1 s2) s5 owner) H5).
  intro.
  generalize (not_reflexive (rec_copy3_trans c0 s1 s2) H0 s0 s5 H6).
  intro.
  cut (s0 <> owner).
  intro.
  generalize (positive_st (rec_copy3_trans c0 s1 s2) s0 s5 H8 H0 H6).
  intro.
  generalize (st_rt (rec_copy3_trans c0 s1 s2) s0 H0 H8 H9).
  intro.
  generalize H5.
  simpl in |- *.
  intro.
  case (eq_site_dec s2 s5).
  intro.
  rewrite e; auto.
  
  intro.
  generalize H11.
  rewrite post_elsewhere.
  intro.
  generalize (inc_dec_in_collect2 (bm c0) copy s5 s1 s2 s0 H3 H12).
  intro.
  generalize (inc_dec_in s0 (bm c0 s5 owner) H13).
  intro.
  generalize (positive_st c0 s0 s5 H8 H H14).
  intro.
  generalize (st_rt c0 s0 H H8 H15).
  intro.
  unfold not in |- *.
  intro.
  rewrite H17 in H16.
  rewrite H16 in H2.
  discriminate.
  
  left; auto.
  
  apply (not_owner_inc3 (rec_copy3_trans c0 s1 s2) s5 owner H0).
  auto.
Qed.

Lemma ancestor_does_not_join2 :
 forall (c0 : Config) (s1 s2 s3 s4 : Site),
 legal c0 ->
 legal (rec_copy3_trans c0 s1 s2) ->
 ancestor (rec_copy3_trans c0 s1 s2) s3 s4 ->
 rt c0 s2 = false ->
 first Message (bm c0 s1 s2) = value Message copy -> s3 <> s2.
Proof.
  intros.
  elim H1.
  intros.
  apply (parent_does_not_join2 c0 s1 s2 s0 s5).
  auto.
  auto.
  auto.
  auto.
  auto.
  intros; auto.
Qed.


Lemma ancestor_not_reflexive :
 forall c : Config,
 legal c -> forall s1 s2 : Site, ancestor c s1 s2 -> s1 <> s2.
Proof.
  intros c H.
  generalize H.
  elim H.
  simpl in |- *.
  intros.
  elim H1.
  intros.
  elim H2.
  simpl in |- *.
  intuition.
  
  simpl in |- *.
  intros.
  elim H4.
  simpl in |- *.
  intuition.
  
  simple induction t.

(*  1*)
  intros.
  apply H1.
  auto.
  
  elim H3.
  simpl in |- *.
  intros.
  apply short.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *; auto.
  
  apply (inc_dec_in_post2 (bm c0) s7 s6 s1 s2 copy).
  generalize H6; simpl in |- *; auto.
  
  discriminate.
  
  intros.
  apply long with (s1 := s5).
  auto.
  
  elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *; auto.
  
  apply (inc_dec_in_post2 (bm c0) s8 s7 s1 s2 copy).
  generalize H8; simpl in |- *; auto.
  
  discriminate.
  
(* 2 *)
  intros.
  apply H1.
  auto.
  
  elim H3.
  simpl in |- *.
  intros.
  apply short.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *; auto.
  
  apply (inc_dec_in_collect2 (bm c0) dec s7 s1 s2 s6).
  auto.
  
  generalize H6; simpl in |- *; auto.
  
  intros.
  apply long with (s1 := s5).
  auto.
  
  elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *; auto.
  
  apply (inc_dec_in_collect2 (bm c0) dec s8 s1 s2 s7).
  auto.
  
  generalize H8; simpl in |- *; auto.
  
(* 3 *)
  intros.
  apply H1.
  auto.
  
  elim H3.
  simpl in |- *.
  intros.
  apply short.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *; auto.
  
  apply (inc_dec_in_collect2 (bm c0) (inc_dec s3) s7 s1 owner s6).
  auto.
  
  apply
   (inc_dec_in_post2 (Collect_message Message (bm c0) s1 owner) s7 s6 owner
      s3 dec).
  generalize H6; simpl in |- *; auto.
  
  discriminate.
  
  intros.
  apply long with (s1 := s5).
  auto.
  
  elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *; auto.
  
  apply (inc_dec_in_collect2 (bm c0) (inc_dec s3) s8 s1 owner s7).
  auto.
  
  apply
   (inc_dec_in_post2 (Collect_message Message (bm c0) s1 owner) s8 s7 owner
      s3 dec).
  generalize H8; simpl in |- *; auto.
  
  discriminate.
  
(* 4 *)
  intros.
  apply H1.
  auto.
  
  elim H3.
  simpl in |- *.
  intros.
  apply short.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *; auto.
  
  apply (inc_dec_in_collect2 (bm c0) copy s7 s1 s2 s6).
  auto.
  
  apply
   (inc_dec_in_post2 (Collect_message Message (bm c0) s1 s2) s7 s6 s2 s1 dec).
  generalize H6; simpl in |- *; auto.
  
  discriminate.
  
  intros.
  apply long with (s1 := s5).
  auto.
  
  elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *; auto.
  
  apply (inc_dec_in_collect2 (bm c0) copy s8 s1 s2 s7).
  auto.
  
  apply
   (inc_dec_in_post2 (Collect_message Message (bm c0) s1 s2) s8 s7 s2 s1 dec).
  generalize H8; simpl in |- *; auto.
  
  discriminate.
  

  (*  5 *)
  simpl in |- *.
  intros.
  case (eq_site_dec s0 s2).
  intro.
  generalize e e0 e1.
  elim H3.
  intro; intro; intro.
  elim H4.
  intros.
  rewrite e4 in H5.
  rewrite e4 in H6.
  rewrite e4.
  generalize (inc_dec_in s5 (bm (rec_copy2_trans c0 s2) s2 owner) H6).
  intro.
  apply not_reflexive with (c := rec_copy2_trans c0 s2).
  auto.
  auto.
  intros.

  apply (ancestor_does_not_join c0 s5 s3 s4).
  auto.
  rewrite e4; auto.
  rewrite e4; auto.
  rewrite e4; auto.
  rewrite e4; auto.


   (* base case when s0!=s2*)
  
  intro.
  apply H1.
  auto.
  
  generalize e.
  generalize n.
  elim H3.
  intros.
  apply short.
  generalize n0.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  generalize H6; simpl in |- *.
  intro.
  apply (inc_dec_in_collect2 (bm c0) copy s6 owner s2 s5).
  auto.
  
  auto.

      (* inductive case when s0!=s1*)
  
  intros.
  apply long with (s1 := s4).
  apply H5.
  apply (parent_does_not_join c0 s2 s4 s5).
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.

  
  generalize n0; elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  generalize H8; simpl in |- *.
  intro.
  apply (inc_dec_in_collect2 (bm c0) copy s7 owner s2 s6).
  auto.
  
  auto.
 

  (*  6 *)

  
  simpl in |- *.
  intros.
  case (eq_site_dec s2 s3).
  intro.
  generalize e e0 e1.
  elim H3.
  intro; intro; intro.
  elim H4.
  intros.
  generalize (inc_dec_in s6 (bm (rec_copy3_trans c0 s1 s2) s7 owner) H6).
  intro.
  apply not_reflexive with (c := rec_copy3_trans c0 s1 s2).
  auto.
  
  auto.
  
  intros.
  rewrite <- e4.
  apply (ancestor_does_not_join2 c0 s1 s2 s4 s5).
  auto.
  auto.
  auto.
  auto.
  auto.
  intro.
  apply H1.
  auto.
  
  generalize e.
  generalize n.
  generalize n1.
  elim H3.
  intros.
  apply short.
  generalize n2 n3 e1.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  generalize H6; simpl in |- *.
  rewrite post_elsewhere.
  intro.
  apply (inc_dec_in_collect2 (bm c0) copy s7 s1 s2 s6).
  auto.
  
  auto.
  
  left; auto.
  
  intros.
  apply long with (s1 := s5).
  apply H5.
  generalize (parent_does_not_join2 c0 s1 s2 s5 s6 H0 H2 H6 e1 e0).
  auto.
  
  auto.
  
  auto.
  
  generalize n2.
  elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *.
  unfold Set_rec_table in |- *; rewrite other_site; auto.
  
  generalize H8; simpl in |- *.
  rewrite post_elsewhere.
  intro.
  apply (inc_dec_in_collect2 (bm c0) copy s8 s1 s2 s7).
  auto.
  
  auto.
  
  left; auto.

  (* 7 *)
  
  intros.
  apply H1.
  auto.
  
  elim H3.
  simpl in |- *.
  intros.
  apply short.
  elim H4.
  intros.
  apply parent_intro.
  generalize H5; simpl in |- *; auto.
  unfold Reset_rec_table in |- *.
  case (eq_site_dec s s5).
  intro; rewrite e1.
  rewrite that_site; auto.
  intro; discriminate.
  
  intro; rewrite other_site; auto.
  
  generalize H6; simpl in |- *.
  intro.
  apply (inc_dec_in_post2 (bm c0) s5 s4 s owner dec).
  auto.
  
  discriminate.
  
  intros.
  apply long with (s1 := s3).
  auto.
  
  elim H6.
  intros.
  apply parent_intro.
  generalize H7; simpl in |- *; auto.
  case (eq_site_dec s s6).
  intro; rewrite e1; unfold Reset_rec_table in |- *; rewrite that_site.
  intro; discriminate.
  
  intro; unfold Reset_rec_table in |- *; rewrite other_site; auto.
  
  generalize H8; simpl in |- *; intro.
  apply (inc_dec_in_post2 (bm c0) s6 s5 s owner dec).
  auto.

  discriminate.
(* Not completed *)
Admitted.

(*
Lemma ancestor_has_positive_st :
 forall c : Config,
 legal c -> forall s1 s2 : Site, ancestor c s1 s2 -> (st c s1 > 0)%Z.
Proof.
  intros.
  elim H0.
  intros.
  elim H1.
  intros.
  generalize (inc_dec_in c s4 (bm c s5 owner) H3).
*)

End INVARIANT6_bis.
