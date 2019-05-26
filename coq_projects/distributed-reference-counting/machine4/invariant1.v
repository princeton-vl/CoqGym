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


Require Export DistributedReferenceCounting.machine4.machine.
Require Export DistributedReferenceCounting.machine4.cardinal.
Require Export DistributedReferenceCounting.machine4.comm.

Unset Standard Proposition Elimination Names.

(** Changes with machine1:
   - As receive table owner equals 1, initally,
     I should add -1
   - Base cases had to be changed
   - inductive case, proof is unchanged
*)
   


Section INVARIANT1.

Remark add_reduce1 :
 forall x1 x2 y : Z, x1 = x2 -> (y + x1 - 1)%Z = (y + x2 - 1)%Z.
Proof.
  intros; omega.
Qed.

Lemma invariant1_init :
 sigma_send_table send_init =
 (sigma_receive_table rec_init + sigma_weight bag_init - 1)%Z.
Proof.
  unfold send_init, rec_init, bag_init in |- *.
  unfold sigma_send_table, sigma_receive_table, sigma_weight in |- *.
  unfold sigma_table in |- *.
  simpl in |- *.
  rewrite sigma_null.
  replace
   (sigma2_table Site LS LS (queue Message) (fun _ _ : Site => cardinal)
      (fun _ _ : Site => empty Message)) with 0%Z.
  rewrite (sigma_sigma_but Site owner eq_site_dec).
  case (eq_site_dec owner owner); intro.
  unfold Int in |- *.
  rewrite sigma_but_null.
  omega.
  
  intros.
  case (eq_site_dec s owner).
  intro; elim H; auto.
  
  auto.
  
  elim n; auto.
  
  apply finite_site.
  
  unfold sigma2_table in |- *.
  unfold sigma_table in |- *.
  symmetry  in |- *.
  simpl in |- *.
  rewrite sigma_null.
  apply sigma_null.
Qed.



Lemma invariant1_inductive :
 forall (c : Config) (t : class_trans c),
 legal c ->
 sigma_send_table (st c) =
 (sigma_receive_table (rt c) + sigma_weight (bm c) - 1)%Z ->
 sigma_send_table (st (transition c t)) =
 (sigma_receive_table (rt (transition c t)) +
  sigma_weight (bm (transition c t)) - 1)%Z.

Proof.
  simple induction t.

  (* 1 *)

  intros; simpl in |- *.
  rewrite sigma_weight_post_message.
  rewrite sigma_inc_send_table.
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.

  (* 2 *)
  
  intros; simpl in |- *.
  rewrite (sigma_weight_collect_message dec).
  rewrite sigma_dec_send_table.
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.
  auto.

  (* 3 *)
  
  intros; simpl in |- *.
  rewrite sigma_weight_post_message.
  rewrite sigma_inc_send_table.
  rewrite sigma_weight_collect_message with (m := inc_dec s3).
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.
  auto.

  (* 4 *)
  
  intros; simpl in |- *.
  rewrite sigma_weight_post_message.
  rewrite sigma_weight_collect_message with (m := copy).
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.
  auto.

  (* 5 *)
  
  intros; simpl in |- *.
  rewrite sigma_weight_collect_message with (m := copy).
  rewrite sigma_set_receive_table.
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.
  auto.
  auto.

  (* 6 *)
  
  intros; simpl in |- *.
  rewrite sigma_weight_post_message.
  rewrite sigma_weight_collect_message with (m := copy).
  rewrite sigma_set_receive_table.
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.
  auto.
  auto.
  
  (* 7 *)

  intros; simpl in |- *.
  rewrite sigma_weight_post_message.
  rewrite sigma_reset_receive_table.
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  rewrite H0; omega.
  auto.


  (* optim 1 *)

  intros; simpl in |- *.
  rewrite sigma_weight_post_message.
  rewrite sigma_weight_change_queue with (s3 := s2).
  unfold cardinal_count in |- *; unfold fun_sum in |- *; simpl in |- *.
  omega.
  auto.

  (* optim 2 *)

  simpl in |- *; intros.
  rewrite H0.
  apply add_reduce1.
  unfold sigma_weight in |- *.
  unfold sigma2_table in |- *.
  apply sigma_table_simpl.
  apply funct_eq.
  intro.
  unfold sigma_table in |- *.
  apply sigma_simpl.
  intros.
  case (eq_queue_dec e1 s1 x s2); intro.
  decompose [and] a.
  rewrite H2; rewrite H3.
  rewrite that_queue.
  rewrite e.
  cut (cardinal (append Message q1 q2) = cardinal (append Message q3 q4)).
  unfold cardinal in |- *.
  rewrite reduce_append.
  rewrite reduce_append.
  omega.
  rewrite e0; auto.
  rewrite other_queue.
  auto.
  auto.
Qed.


Lemma invariant1 :
 forall c : Config,
 legal c ->
 sigma_send_table (st c) =
 (sigma_receive_table (rt c) + sigma_weight (bm c) - 1)%Z.
Proof.
  intros.
  elim H.
  apply invariant1_init.
  exact invariant1_inductive.
Qed.




End INVARIANT1.

