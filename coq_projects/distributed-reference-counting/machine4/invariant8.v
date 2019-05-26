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


Require Export DistributedReferenceCounting.machine4.invariant5.
Require Export DistributedReferenceCounting.machine4.invariant7.

Unset Standard Proposition Elimination Names.

(* changes:
   In safety1 and safety2, I had to use 
   sigma_but_strictly_positive, instead of sigma_strictly_positive.

   In safety2, the case ~s2=owner should not be isolated
*)


Lemma direct_son_is_positive :
 forall c : Config,
 legal c ->
 forall s : Site,
 direct_son c s ->
 (Int (rt c s) + reduce Message dec_count (bm c s owner) +
  reduce Message copy_count (bm c owner s) -
  reduce Message new_inc_count (bm c s owner) > 0)%Z.


Proof.
  intros.
  elim H0.
  intros.
  rewrite H2; unfold Int in |- *.
  generalize (not_inc_dec_in (bm c s0 owner) H3); intro.
  generalize (copy_count_is_positive (bm c owner s0)).
  intro.
  generalize (dec_count_is_positive (bm c s0 owner)); intro.
  cut (reduce Message new_inc_count (bm c s0 owner) = 0%Z).
  intro.
  omega.
  
  generalize H4.
  elim (bm c s0 owner).
  simpl in |- *; auto.
  
  intro.
  case d.
  simpl in |- *.
  intros.
  rewrite H7.
  auto.
  
  intro.
  generalize (H8 s1).
  intuition.
  
  intros.
  elim (H8 s1); simpl in |- *.
  left; auto.
  
  simpl in |- *; intros.
  rewrite H7.
  omega.
  
  intro.
  generalize (H8 s1).
  intuition.
Qed.

Remark add_reduce : forall x : Z, (x > 0)%Z -> (x + 1 - 1 > 0)%Z.
Proof.
  intro; omega.
Qed.

Lemma safety1 :
 forall c : Config,
 legal c ->
 forall s : Site, s <> owner -> rt c s = true -> (st c owner > 0)%Z.

Proof.
  intros.
  rewrite (invariant4 c H).
  rewrite other_definition_for_sigma_receive_table.
  rewrite <- sigma_same_table.
  rewrite <- sigma_same_table.
  rewrite <- sigma_same_table2.
  unfold Z_id in |- *.
  unfold fun_minus in |- *.
  unfold fun_sum in |- *.
  rewrite sigma_sigma_but_owner.
  rewrite owner_rt_true.
  rewrite empty_q_to_me.
  simpl in |- *.
  simpl in |- *.
  elim (direct_or_indirect_son1 c s H0 H1); intro.
  unfold sigma_table_but_owner in |- *.
  apply add_reduce.
  apply sigma_but_strictly_positive with (x := s).
  apply in_s_LS.
  
  auto.
  
  intro; apply invariant5; auto.
  
  apply direct_son_is_positive; auto.
  
  apply add_reduce.
  elim (parent_invariant c H s b).
  intros.
  decompose [and] H2.
  unfold sigma_table_but_owner in |- *.
  apply sigma_but_strictly_positive with (x := x).
  apply in_s_LS.
  
  elim H3.
  intros; auto.
  
  intro; apply invariant5; auto.
  
  apply direct_son_is_positive; auto.
  
  auto.
  
  auto.
Qed.


Lemma safety2 :
 forall c : Config,
 legal c ->
 forall s1 s2 : Site,
 In_queue Message copy (bm c s1 s2) -> (st c owner > 0)%Z.
Proof.
  intros.
  elim (decide_inc_dec_in_queue c s2); intro.
  elim a; intros.
  apply safety1 with (s := x).
  auto.
  
  apply (not_owner_inc3 c s2 owner H x).
  apply inc_dec_in; auto.
  
  generalize (inc_dec_in x (bm c s2 owner) p).
  intro.
  generalize (not_owner_inc3 c s2 owner H x H1).
  intro.
  generalize (positive_st c x s2 H2 H H1).
  intro.
  generalize (st_rt c x H H2 H3).
  auto.
  
  case (eq_site_dec s1 owner); intro.
  rewrite (invariant4 c H).
  rewrite other_definition_for_sigma_receive_table.
  rewrite <- sigma_same_table.
  rewrite <- sigma_same_table.
  rewrite <- sigma_same_table2.
  unfold Z_id in |- *.
  unfold fun_minus in |- *.
  unfold fun_sum in |- *.
  rewrite sigma_sigma_but_owner.
  rewrite owner_rt_true.
  rewrite empty_q_to_me.
  simpl in |- *.
  apply add_reduce.
  unfold sigma_table_but_owner in |- *.
  apply sigma_but_strictly_positive with (x := s2).
  apply in_s_LS.
  
  unfold not in |- *; intro; generalize H0.
  rewrite e; rewrite H1; rewrite empty_q_to_me; simpl in |- *.
  auto.
  
  auto.
  
  intro; apply invariant5; auto.
  
  generalize (dec_count_is_positive (bm c s2 owner)); intro.
  cut (Int (rt c s2) >= 0)%Z.
  intro.
  cut (reduce Message new_inc_count (bm c s2 owner) = 0%Z).
  intro.
  cut (reduce Message copy_count (bm c owner s2) > 0)%Z.
  intro.
  omega.
  
  apply reduce_in_queue_strictly_positive with (x := copy).
  intro; unfold copy_count in |- *.
  case a; intros.
  omega.
  
  omega.
  
  omega.
  
  exact eq_message_dec.
  
  unfold copy_count in |- *; simpl in |- *.
  omega.
  
  rewrite <- e; auto.
  
  generalize (not_inc_dec_in (bm c s2 owner) b).
  intros.
  apply reduce_in_queue_null.
  intro.
  case x; simpl in |- *; intros.
  auto.
  
  elim (H3 s); auto.
  
  auto.
  
  unfold Int in |- *.
  case (eq_bool_dec (rt c s2)).
  intro.
  rewrite e0; simpl in |- *; omega.
  
  intro; rewrite e0; simpl in |- *; omega.
  
  auto.
  
  auto.
  
  apply safety1 with (s := s1).
  auto.
  
  auto.
  
  apply st_rt.
  auto.
  
  auto.
  
  rewrite invariant2.
  unfold sigma_rooted in |- *.
  apply sigma2_strictly_positive with (x := s1) (y := s2).
  exact eq_site_dec.
  
  apply in_s_LS.
  
  apply in_s_LS.
  
  unfold rooted in |- *; intros.
  apply reduce_positive_or_null.
  intros.
  apply rooted_fun_positive_or_null.
  
  unfold rooted in |- *.
  apply reduce_in_queue_strictly_positive with (x := copy).
  intro.
  apply rooted_fun_positive_or_null.
  
  exact eq_message_dec.
  
  unfold rooted_fun in |- *.
  case (eq_site_dec s1 s1); intro.
  omega.
  
  elim n0.
  auto.
  
  auto.
  
  auto.
  
  auto.
Qed.
