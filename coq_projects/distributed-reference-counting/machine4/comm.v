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


(* Communications *)

(* Without specifying how messages are defined, I am constructing
general Lemma in terms of reduce *)

Require Export reduce.
Require Export DistributedReferenceCounting.machine4.cardinal.
Require Export sigma2.
Require Export sum.

Unset Standard Proposition Elimination Names.

Section CARDINAL_EFFECT.

(* This section is really using the inductive type Message *)
Let Bag_of_message := Bag_of_Data Message.

Variable inc_fun : Site -> Z.

Lemma cardinal_post_message :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 cardinal (Post_message Message m b s1 s2 s1 s2) =
 (cardinal (b s1 s2) + cardinal_count m)%Z.
Proof.
  intros.
  unfold cardinal in |- *.
  apply reduce_post_message.
Qed.

Lemma cardinal_collect_message :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 first Message (b s1 s2) = value Message m ->
 cardinal (Collect_message Message b s1 s2 s1 s2) =
 (cardinal (b s1 s2) - cardinal_count m)%Z.
Proof.
  intros.
  unfold cardinal in |- *.
  apply reduce_collect_message.
  auto.
Qed.

End CARDINAL_EFFECT.


Section WEIGHT_EFFECT2.

Lemma sigma_weight_post_message :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 sigma_weight (Post_message Message m b s1 s2) =
 (sigma_weight b + cardinal_count m)%Z.
Proof.
  unfold sigma_weight in |- *.
  unfold Post_message in |- *.
  unfold change_queue in |- *.
  intros.
  rewrite sigma_table2_change.
  simpl in |- *.
  omega.
  apply finite_site.
  apply finite_site.
Qed.

Lemma sigma_weight_collect_message :
 forall (m : Message) (s1 s2 : Site) (b : Bag_of_message),
 first Message (b s1 s2) = value Message m ->
 sigma_weight (Collect_message Message b s1 s2) =
 (sigma_weight b - cardinal_count m)%Z.
Proof.
  unfold sigma_weight in |- *.
  unfold Collect_message in |- *.
  unfold change_queue in |- *.
  intros.
  rewrite sigma_table2_change.
  rewrite cardinal_first_out with (m := m).
  omega.
  auto.
  apply finite_site.
  apply finite_site.
Qed.

Remark add_reduce :
 forall x y z w a : Z, x = a -> (x + y)%Z = (a + (y + z + w) - w - z)%Z.
Proof.
intros; omega.
Qed.


Lemma sigma_weight_change_queue :
 forall (s1 s2 s3 : Site) (b : Bag_of_message) (q : queue Message),
 b s1 s2 = input Message dec (input Message (inc_dec s3) q) ->
 sigma_weight (change_queue (queue Message) b s1 s2 q) =
 (sigma_weight b - cardinal_count dec - cardinal_count (inc_dec s3))%Z.
Proof.
  intros.
  unfold sigma_weight in |- *.
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s1)
                        (s1 := s2)
                        (eq_site_dec := eq_site_dec).
  rewrite
   sigma2_sigma2_but_x_y
                         with
                         (s0 := s1)
                        (s1 := s2)
                        (eq_site_dec := eq_site_dec).
  unfold cardinal in |- *.
  rewrite that_queue.
  rewrite H.
  simpl in |- *.
  apply add_reduce.
  apply sigma2_but_simpl2.
  intros.
  case (eq_queue_dec s1 x s2 y); intro.
  elim H0.
  split; decompose [and] a; auto.
  
  rewrite other_queue.
  auto.
  
  elim o; auto.
  
  apply finite_site.
  
  apply finite_site.
  
  apply finite_site.
  
  apply finite_site.
  
  apply finite_site.
  
  apply finite_site.
Qed.

End WEIGHT_EFFECT2.
