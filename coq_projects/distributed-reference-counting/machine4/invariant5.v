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


Require Export DistributedReferenceCounting.machine4.alternate.
Require Export DistributedReferenceCounting.machine4.invariant0.
Require Export DistributedReferenceCounting.machine4.invariant1.
Require Export DistributedReferenceCounting.machine4.invariant2.
Require Export DistributedReferenceCounting.machine4.invariant3.
Require Export DistributedReferenceCounting.machine4.invariant4.

Unset Standard Proposition Elimination Names.

(* Changes
   - proof of  1  for false_rt_D_queue.
   - proof of  1  for  legal_alternate.
   - owner_st_positive and its proof.
*)

Section INVARIANT5.

(* In this file, we establish the following inequality
   Int + Sum copy + Sum dec - Sum inc_dec >= 0

*) 


(* The message queue between a site and the owner has a particular
structure.  Messages dec and inc_dec are alternated.
 *)


Lemma legal_alternate :
 forall (s : Site) (c : Config),
 legal c ->
 alternate (bm c s owner) /\ (rt c s = false -> D_queue (bm c s owner)).
Proof.  
  intros.
  elim H.
  split.
  apply alt_null.
  
  simpl in |- *.
  intro.
  apply D_empty.
  
  (* 1 *)

  simple induction t; simpl in |- *; intros.
  decompose [and] H1.
  split.
  case (eq_queue_dec s1 s s2 owner); intro.
  decompose [and] a0.
  rewrite H4; rewrite H5; rewrite post_here.
  apply alt_any_alt; auto.
  intro; discriminate.
  
  rewrite post_elsewhere.
  auto.
  
  auto.
  
  case (eq_site_dec s1 s); intro.
  generalize a; unfold access in |- *.
  rewrite e.
  intros.
  rewrite H4 in a0.
  discriminate.
  
  rewrite post_elsewhere.
  auto.
  
  left; auto.
  
    
    (* 2 *)
  decompose [and] H1.
  split.
  apply alt_collect; auto.
  
  intro.
  apply D_collect; auto.
    
    (* 3 *)
  
  decompose [and] H1.
  split.
  apply alt_post_elsewhere.
  right.
  apply (not_owner_inc3 c0 s1 owner H0 s3).
  apply first_in.
  auto.
  
  apply alt_collect; auto.
  
  intro.
  apply D_post_elsewhere.
  right.
  apply (not_owner_inc3 c0 s1 owner H0 s3).
  apply first_in.
  auto.
  
  apply D_collect.
  apply H3.
  auto.
    
    (* 4 *)
  
  split.
  decompose [and] H1.
  case (eq_queue_dec s2 s s1 owner); intros.
  decompose [and] a.
  rewrite H4; rewrite H5.
  apply alt_post_any.
  intro; discriminate.
  
  apply alt_collect; auto.
  
  apply alt_post_elsewhere; auto.
  apply alt_collect; auto.
  
  decompose [and] H1.
  intro.
  case (eq_queue_dec s2 s s1 owner); intros; simpl in |- *.
  decompose [and] a.
  rewrite H5; rewrite H6.
  apply D_post_dec.
  apply alt_collect.
  decompose [and] H1; auto.
  
  rewrite post_elsewhere.
  apply D_collect.
  apply H3.
  auto.
  
  auto.
    
    (* 5 *)
    
  decompose [and] H1; split.
  apply alt_collect; trivial.
  
  case (eq_site_dec s s2); intro.
  rewrite e1; unfold Set_rec_table in |- *; rewrite that_site.
  intro; discriminate.
  
  intro.
  apply D_collect.
  apply H3.
  generalize H4; unfold Set_rec_table in |- *; rewrite other_site; auto.
    
    (* 6 *)
  
  decompose [and] H1; split.
  case (eq_site_dec s2 s); intro.
  rewrite e1; apply alt_post_inc.
  apply alt_collect; trivial.
  
  rewrite collect_elsewhere.
  rewrite e1 in e.
  generalize (H3 e).
  intro.
  elim H4.
  auto.
  
  simpl in |- *.
  intros.
  auto.

auto.
  
  rewrite <- e1.
  auto.
  
  apply alt_post_elsewhere; auto.
  apply alt_collect; trivial.
  
  case (eq_site_dec s s2); intro.
  rewrite e1; unfold Set_rec_table in |- *; rewrite that_site; intro;
   discriminate.
  
  intro.
  apply D_post_elsewhere; auto.
  apply D_collect; auto.
  apply H3.
  generalize H4; unfold Set_rec_table in |- *; rewrite other_site; auto.
  
    (* 7 *)
  decompose [and] H1; split.
  case (eq_site_dec s0 s); intro.
  rewrite e1; apply alt_post_any; auto.
  intro; discriminate.
  
  apply alt_post_elsewhere; auto.
  
  case (eq_site_dec s0 s); intro.
  intro.
  rewrite e1.
  apply D_post_dec.
  auto.
  
  unfold Reset_rec_table in |- *; rewrite other_site.
  intro.
  apply D_post_elsewhere; auto.
  
  auto.
  
  (* optim 1 *)

  decompose [and] H1; split.
  rewrite post_elsewhere.
  case (eq_site_dec s1 s); intro.
  rewrite e0.
  rewrite that_queue.
  rewrite e0 in e.
  rewrite e in H2.
  inversion H2.
  inversion H7.
  auto.
  
  auto.
  
  rewrite other_queue.
  auto.
  
  auto.
  
  right.
  apply (not_owner_inc3 c0 s1 owner).
  auto.
  
  rewrite e; simpl in |- *.
  right; left; auto.
  
  intro.
  rewrite post_elsewhere.
  case (eq_site_dec s1 s); intro.
  rewrite e0.
  rewrite that_queue.
  generalize (H3 H4).
  rewrite <- e0; rewrite e.
  intro.
  inversion H5.
  inversion H6.
  inversion H12.
  elim (H15 s2).
  auto.
  
  apply D_dec.
  auto.
  
  auto.
  
  rewrite other_queue.
  apply H3; auto.
  
  auto.
  
  right.
  apply (not_owner_inc3 c0 s1 owner).
  auto.
  
  rewrite e.
  simpl in |- *.
  right; left; auto.

  (* optim 2 *)

  decompose [and] H1; split.
  case (eq_queue_dec s1 s s2 owner); intro.
  decompose [and] a.
  rewrite H4; rewrite H5.
  rewrite that_queue.
  apply alt_shuffle_copy with (q1 := q1) (q2 := q2).
  auto.
  
  generalize H2.
  rewrite H4 in e; rewrite H5 in e.
  rewrite e.
  auto.
  rewrite other_queue.
  auto.
  elim o; intro; auto.
  intro.
  case (eq_queue_dec s1 s s2 owner); intro.
  decompose [and] a.
  rewrite H5; rewrite H6.
  rewrite that_queue.
  apply D_shuffle_copy with (q1 := q1) (q2 := q2).
  auto.
  rewrite <- e.
  rewrite H5; rewrite H6.
  apply H3; auto.
  rewrite other_queue.
  apply H3; auto.
  elim o; intro; auto.
Qed.


Lemma count_alt_queue :
 forall q : queue Message,
 alternate q ->
 (reduce Message dec_count q + 1 >= reduce Message new_inc_count q)%Z /\
 (D_queue q ->
  (reduce Message dec_count q >= reduce Message new_inc_count q)%Z).
Proof.
  intros.
  elim H.
  simpl in |- *.
  split.
  omega.
  
  intro; omega.
  
  intros.
  simpl in |- *.
  split.
  cut (dec_count m >= 0)%Z.
  intro.
  cut (new_inc_count m = 0%Z).
  intro.
  omega.
  
  unfold new_inc_count in |- *.
  generalize H0.
  case m; intros.
  auto.
  
  elim (H4 s); auto.
  
  auto.
  
  elim m; simpl in |- *; intros; omega.
  
  intro.
  decompose [and] H2.
  generalize H0 H3.
  case m; simpl in |- *; intros.
  omega.
  
  elim (H6 s).
  auto.
  
  simpl in |- *.
  cut (D_queue qm).
  intro.
  generalize (H5 H8); intro.
  omega.
  
  apply D_input.
  auto.
  
  simpl in |- *; intros.
  split.
  decompose [and] H1.
  cut (D_queue qm).
  intro.
  generalize (H4 H5); omega.
  
  apply D_dec.
  auto.
  
  auto.
  
  intro.
  inversion H3.
  generalize H5; simpl in |- *.
  case (eq_bool_dec true); intro.
  intro; contradiction.
  
  discriminate.
Qed.


Lemma count_inc_and_dec_alt_queue :
 forall q : queue Message,
 alternate q ->
 (reduce Message dec_count q + 1 >= reduce Message new_inc_count q)%Z.
Proof.
  intros.
  intros.
  generalize (count_alt_queue q H); intro.
  decompose [and] H0.
  auto.
Qed.


Lemma count_inc_and_dec_D_queue :
 forall q : queue Message,
 D_queue q ->
 (reduce Message dec_count q >= reduce Message new_inc_count q)%Z.
Proof.
  intros.
  generalize (D_queue_is_alternate q H); intro.
  generalize (count_alt_queue q H0); intro.
  decompose [and] H1.
  apply H3.
  auto.
Qed.


Lemma copy_count_is_positive :
 forall q : queue Message, (reduce Message copy_count q >= 0)%Z.
Proof.
  intros.
  apply reduce_positive_or_null.
  intro.
  elim a; simpl in |- *; intros; omega.
Qed.

Lemma dec_count_is_positive :
 forall q : queue Message, (reduce Message dec_count q >= 0)%Z.
Proof.
  intros.
  apply reduce_positive_or_null.
  intro.
  elim a; simpl in |- *; intros; omega.
Qed.


Lemma invariant5 :
 forall c : Config,
 legal c ->
 forall s : Site,
 (Int (rt c s) + reduce Message dec_count (bm c s owner) +
  reduce Message copy_count (bm c owner s) -
  reduce Message new_inc_count (bm c s owner) >= 0)%Z.

Proof.
  intros.
  generalize (copy_count_is_positive (bm c owner s)); intro.
  generalize (legal_alternate s c H); intro.
  case (eq_bool_dec (rt c s)); intro; rewrite e; unfold Int in |- *.
  decompose [and] H1.
  generalize (count_inc_and_dec_alt_queue (bm c s owner) H2); intro.
  omega.
  decompose [and] H1.
  generalize (H3 e); intro.
  generalize (count_inc_and_dec_D_queue (bm c s owner) H4); intro.
  omega.
Qed.




Let Recv_T := Site -> bool.

Lemma other_definition_for_sigma_receive_table :
 forall t : Recv_T,
 sigma_receive_table t =
 sigma_table Site LS Z (Z_id Site) (fun s : Site => Int (t s)).
Proof.
  intros.
  unfold sigma_receive_table in |- *.
  unfold sigma_table in |- *.
  unfold Z_id in |- *.
  auto.
Qed.


Remark add_reduce : forall x : Z, (x + 1 - 1)%Z = x.
Proof.
  intro; omega.
Qed.


Lemma owner_st_positive : forall c : Config, legal c -> (st c owner >= 0)%Z.
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
  rewrite add_reduce.
  unfold sigma_table_but_owner in |- *.
  apply sigma_but_pos.
  exact (invariant5 c H).
  auto.
  auto.
Qed.



End INVARIANT5.
