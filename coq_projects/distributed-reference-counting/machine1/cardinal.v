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


(* this file contains some cardinal functions, which are message
dependent *)

Require Export reduce.
Require Export DistributedReferenceCounting.machine1.machine.


Section COUNT_MESSAGE.

Definition dec_predicate (m : Message) :=
  match m with
  | dec => true
  | _ => false
  end.

Definition inc_predicate (m : Message) :=
  match m with
  | inc_dec _ => true
  | _ => false
  end.

(* the next one only recognises inc_dec messages related to s0 *)

Variable s0 : Site.

Definition site_inc_predicate (m : Message) :=
  match m with
  | inc_dec s => if eq_site_dec s s0 then true else false
  | _ => false
  end.


Definition copy_predicate (m : Message) :=
  match m with
  | copy => true
  | _ => false
  end.

Definition dec_count (m : Message) :=
  match m with
  | dec => 1%Z
  | _ => 0%Z
  end.

Definition inc_count (m : Message) := 0%Z.

Definition copy_count (m : Message) :=
  match m with
  | copy => 1%Z
  | _ => 0%Z
  end.

Definition cardinal_count :=
  fun_sum Message dec_count (fun_sum Message inc_count copy_count).


Definition cardinal := reduce Message cardinal_count.

Lemma disjoint_cardinal :
 forall q : queue Message,
 cardinal q =
 (reduce Message dec_count q +
  (reduce Message inc_count q + reduce Message copy_count q))%Z.
Proof.
  intro.
  rewrite <- disjoint_reduce.
  rewrite <- disjoint_reduce.
  unfold cardinal in |- *.
  unfold cardinal_count in |- *.
  auto.
Qed.

Lemma cardinal_first_out :
 forall (q : queue Message) (m : Message),
 first Message q = value Message m ->
 cardinal (first_out Message q) = (cardinal q - cardinal_count m)%Z.
Proof.
  intros.
  unfold cardinal in |- *.
  apply reduce_first_out.
  auto.
Qed.

End COUNT_MESSAGE.




Section SIG_WEIGHT.
Let Bag_of_message := Bag_of_Data Message.

Definition sigma_weight (bm : Bag_of_message) :=
  sigma2_table Site LS LS (queue Message) (fun s1 s2 : Site => cardinal) bm.

End SIG_WEIGHT.

