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


Set Implicit Arguments.
Unset Strict Implicit.
Require Export Union.
(** Title "Intersection of two parts." *)
Section Inter1.
Variable E : Setoid.

Definition inter : part_set E -> part_set E -> part_set E.
intros A B.
apply (Build_Predicate (Pred_fun:=fun x : E => in_part x A /\ in_part x B)).
red in |- *.
intros x y H' H'0; try assumption.
elim H'; intros H'1 H'2; try exact H'1; clear H'.
split; [ try assumption | idtac ].
apply in_part_comp_l with x; auto with algebra.
apply in_part_comp_l with x; auto with algebra.
Defined.

Lemma included_inter_l : forall A B : part_set E, included (inter A B) A.
unfold included in |- *; simpl in |- *; intuition.
Qed.

Lemma included_inter_r : forall A B : part_set E, included (inter A B) B.
unfold included in |- *; simpl in |- *; intuition.
Qed.

Lemma in_part_inter_l :
 forall (A B : part_set E) (x : E), in_part x (inter A B) -> in_part x A.
simpl in |- *; intuition.
Qed.

Lemma in_part_inter_r :
 forall (A B : part_set E) (x : E), in_part x (inter A B) -> in_part x B.
simpl in |- *; intuition.
Qed.

Lemma in_part_inter :
 forall (A B : part_set E) (x : E),
 in_part x A -> in_part x B -> in_part x (inter A B).
simpl in |- *. intuition.
Qed.

Lemma inter_not_in_l :
 forall (A B : part_set E) (x : E), ~ in_part x A -> ~ in_part x (inter A B).
simpl in |- *; intuition.
Qed.

Lemma inter_not_in_r :
 forall (A B : part_set E) (x : E), ~ in_part x B -> ~ in_part x (inter A B).
simpl in |- *; intuition.
Qed.

Lemma included2_inter :
 forall A B C : part_set E,
 included A C -> included B C -> included (inter A B) C.
unfold included in |- *; simpl in |- *; intuition.
Qed.

Lemma inter_comp :
 forall A A' B B' : part_set E,
 Equal A A' -> Equal B B' -> Equal (inter A B) (inter A' B').
unfold inter in |- *; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros A A' B B' H' H'0 x.
generalize (H' x) (H'0 x); tauto.
Qed.

Lemma inter_assoc :
 forall A B C : part_set E, Equal (inter A (inter B C)) (inter (inter A B) C).
simpl in |- *. unfold eq_part in |- *. simpl in |- *.
tauto.
Qed.

Lemma inter_com : forall A B : part_set E, Equal (inter A B) (inter B A).
simpl in |- *. unfold eq_part in |- *; simpl in |- *.
tauto.
Qed.

Parameter
  inter_union_dist_r :
    forall A B C : part_set E,
    Equal (inter (union A B) C) (union (inter A C) (inter B C)).
Parameter
  inter_union_dist_l :
    forall A B C : part_set E,
    Equal (inter A (union B C)) (union (inter A B) (inter A C)).
End Inter1.
Hint Resolve included_inter_l included_inter_r in_part_inter_l
  in_part_inter_r in_part_inter included2_inter inter_comp inter_assoc
  inter_not_in_l inter_not_in_r inter_union_dist_r inter_union_dist_l:
  algebra.
Hint Immediate inter_com: algebra.