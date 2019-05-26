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

Require Export DistributedReferenceCounting.machine2.alternate.
Require Export DistributedReferenceCounting.machine2.invariant0.
Require Export DistributedReferenceCounting.machine2.invariant1.
Require Export DistributedReferenceCounting.machine2.invariant2.
Require Export DistributedReferenceCounting.machine2.invariant3.
Require Export DistributedReferenceCounting.machine2.invariant4.

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


Lemma false_rt_D_queue :
 forall (c : Config) (s : Site),
 legal c -> rt c s = false -> D_queue (bm c s owner).
Proof.
   intros c s H; elim H.
   simpl in |- *.
   intro.
   apply D_empty.
   
   simple induction t; simpl in |- *; intros.

   (*  1 *)

   case (eq_queue_dec s1 s s2 owner); intro.
   decompose [and] a0.
   generalize a; rewrite H3; unfold access in |- *.
   rewrite H2; intro.
   discriminate.


   apply D_post_elsewhere; auto.

   (*  2 *)
   apply D_collect; auto.
   
   (*  3 *)

   apply D_post_elsewhere.
   right.
   apply (not_owner_inc3 c0 s1 owner H0 s3).
   apply first_in.
   auto.
   apply D_collect.
   auto.
   
   (*  4 *)

   case (eq_queue_dec s2 s s1 owner); intros; simpl in |- *.
   decompose [and] a.
   rewrite H3; rewrite H4.
   apply D_post_dec.
   
   apply D_post_elsewhere.
   auto.

   apply D_collect; auto.
   
   (* 5 *)

   case (eq_site_dec s s2); intro.
   generalize H2; rewrite e1; unfold Set_rec_table in |- *; rewrite that_site.
   intro; discriminate.
   
   apply D_collect.
   apply H1.
   generalize H2; unfold Set_rec_table in |- *; rewrite other_site; auto.

   (*  6 *)
   
   case (eq_site_dec s s2); intro.
   generalize H2; rewrite e1; unfold Set_rec_table in |- *; rewrite that_site;
    intro; discriminate.
   
   apply D_post_elsewhere; auto.
   apply D_collect; auto.
   apply H1; generalize H2; unfold Set_rec_table in |- *; rewrite other_site;
    auto.

   (*  7 *)
   
   case (eq_site_dec s0 s); intro.
   rewrite e1; apply D_post_dec.
   
   apply D_post_elsewhere; auto.
   apply H1; generalize H2; unfold Reset_rec_table in |- *;
    rewrite other_site; auto.
Qed.


Lemma legal_alternate :
 forall (s : Site) (c : Config), legal c -> alternate (bm c s owner).
Proof.  
  intros; elim H.
  apply alt_null.
  
  simple induction t; simpl in |- *; intros.
  
  (* 1 *)

  case (eq_queue_dec s1 s s2 owner); intro.
  decompose [and] a0.
  rewrite H2; rewrite H3; rewrite post_here.
  apply alt_any_alt; auto.
  intro; discriminate.
  
  rewrite post_elsewhere.
  auto.
  
  auto.
  
  (* 2 *)
  apply alt_collect; auto.
  
  (* 3 *)
  apply alt_post_elsewhere.
  right.
  apply (not_owner_inc3 c0 s1 owner H0 s3).
  apply first_in.
  auto.
  apply alt_collect; auto.
  
  (* 4 *)
  
  case (eq_queue_dec s2 s s1 owner); intros.
  decompose [and] a.
  rewrite H2; rewrite H3.
  apply alt_post_any.
  intro; discriminate.
  
  apply alt_collect; auto.
  
  apply alt_post_elsewhere; auto.
  apply alt_collect; auto.
  
  (* 5 *)
  
  apply alt_collect; trivial.
  
  (* 6 *)
  
  case (eq_site_dec s2 s); intro.
  rewrite e1; apply alt_post_inc.
  apply alt_collect; trivial.
  rewrite collect_elsewhere.
  generalize (false_rt_D_queue c0 s2 H0 e); intro.
  rewrite e1 in H2.
  elim H2.
  auto.
  auto.
  case (eq_site_dec s1 s); intro.
  rewrite e2 in n; auto.
  auto.
  apply alt_post_elsewhere; auto.
  apply alt_collect; trivial.
  
  (* 7 *)
  
  case (eq_site_dec s0 s); intro.
  rewrite e1; apply alt_post_any; auto.
  intro; discriminate.
  
  apply alt_post_elsewhere; auto.
Qed.

Lemma count_inc_and_dec_alt_queue :
 forall q : queue Message,
 alternate q ->
 (reduce Message dec_count q + 1 >= reduce Message new_inc_count q)%Z.
Proof.
  intros.
  elim H.
  simpl in |- *; omega.
  
  intro; simpl in |- *; omega.
  
  simpl in |- *; intros.
  generalize H0; case m; simpl in |- *.
  intro; omega.
  
  intros.
  elim (H3 s); auto.
  
  intro; omega.
  
  simpl in |- *; intros.
  omega.
Qed.


Lemma count_inc_and_dec_D_queue :
 forall q : queue Message,
 alternate q ->
 D_queue q ->
 (reduce Message dec_count q >= reduce Message new_inc_count q)%Z.
Proof.
  intros q H.
  elim H; intros.
  simpl in |- *; omega.
  
  absurd (D_queue (input Message (inc_dec s0) (empty Message))).
  apply not_D_queue.
  discriminate.
  auto.
  
  generalize H3.
  case m.
  intro; simpl in |- *.
  generalize (count_inc_and_dec_alt_queue qm H1); intro; omega.
  
  intros.
  absurd (D_queue (input Message (inc_dec s) qm)).
  apply not_D_queue.
  discriminate.
  auto.
  
  intros.
  absurd (D_queue (input Message copy qm)).
  apply not_D_queue.
  discriminate.
  auto.
  
  absurd (D_queue (input Message (inc_dec s0) (input Message dec qm))).
  apply not_D_queue.
  discriminate.
  
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
  generalize (count_inc_and_dec_alt_queue (bm c s owner) H1); intro.
  omega.
  
  generalize (false_rt_D_queue c s H e); intro.
  generalize (count_inc_and_dec_D_queue (bm c s owner) H1 H2); intro.
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
