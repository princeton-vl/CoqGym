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
Require Export DistributedReferenceCounting.machine3.cardinal.
Require Export sigma2.
Require Export sum.

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

End WEIGHT_EFFECT2.
