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


Require Export reduce.
Require Export table.
Require Export abstract_machine.

Section SUM_REDUCE.

Variable Data : Set.

Variable s0 : Site.

Let Bag_of_message := Bag_of_Data Data.

Variable f : Data -> Z.



Definition sigma_reduce (bom : Bag_of_message) :=
  sigma Site LS (fun si : Site => reduce Data f (bom s0 si)). 



Lemma sigma_reduce_pos :
 forall (s0 s1 : Site) (bom : Bag_of_message),
 (forall m : Data, (f m > 0)%Z) -> (sigma_reduce bom >= 0)%Z.
Proof.
  intros s1 s2 bom H.
  unfold sigma_reduce in |- *.
  apply sigma_pos.
  intro x_.
  apply reduce_positive.
  auto.
Qed.

End SUM_REDUCE.