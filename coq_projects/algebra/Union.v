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
Require Export Parts.
(** Title "Union of two parts.".*)
Section Union1.
Variable E : Setoid.

Definition union : part_set E -> part_set E -> part_set E.
intros A B.
apply (Build_Predicate (Pred_fun:=fun x : E => in_part x A \/ in_part x B)).
red in |- *.
intros x y H' H'0; try assumption.
elim H'; [ intros H'1; try exact H'1; clear H' | intros H'1; clear H' ].
left; try assumption.
apply in_part_comp_l with x; auto with algebra.
right; try assumption.
apply in_part_comp_l with x; auto with algebra.
Defined.

Lemma included_union_l : forall A B : part_set E, included A (union A B).
unfold included in |- *; simpl in |- *; intuition.
Qed.

Lemma included_union_r : forall A B : part_set E, included B (union A B).
unfold included in |- *; simpl in |- *; intuition.
Qed.

Lemma in_part_union_l :
 forall (A B : part_set E) (x : E), in_part x A -> in_part x (union A B).
simpl in |- *; intuition.
Qed.

Lemma in_part_union_r :
 forall (A B : part_set E) (x : E), in_part x B -> in_part x (union A B).
simpl in |- *; intuition.
Qed.
Parameter
  in_part_union_or :
    forall (A B : part_set E) (x : E),
    in_part x A \/ in_part x B -> in_part x (union A B).

Lemma in_part_union :
 forall (A B : part_set E) (x : E),
 in_part x (union A B) -> in_part x A \/ in_part x B.
intros A B x; try assumption.
unfold union in |- *; intuition.
Qed.

Lemma union_not_in_l :
 forall (A B : part_set E) (x : E),
 in_part x (union A B) -> ~ in_part x A -> in_part x B.
unfold union in |- *; simpl in |- *; intuition.
Qed.

Lemma included2_union :
 forall A B C : part_set E,
 included A C -> included B C -> included (union A B) C.
unfold included in |- *; simpl in |- *; intuition.
Qed.

Lemma union_comp :
 forall A A' B B' : part_set E,
 Equal A A' -> Equal B B' -> Equal (union A B) (union A' B').
unfold union in |- *; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros A A' B B' H' H'0 x; split; [ intros H'1; try assumption | idtac ].
elim H'1; [ intros H'2; try exact H'2; clear H'1 | intros H'2; clear H'1 ].
left; try assumption.
elim (H' x); intros H'3 H'4; lapply H'3;
 [ intros H'5; try exact H'5; clear H'3 | clear H'3 ].
auto with algebra.
right; try assumption.
elim (H'0 x); intros H'3 H'4; lapply H'3;
 [ intros H'5; try exact H'5; clear H'3 | clear H'3 ].
auto with algebra.
intros H'1; try assumption.
elim H'1; [ intros H'2; try exact H'2; clear H'1 | intros H'2; clear H'1 ].
left; try assumption.
elim (H' x); intros H'3 H'4; lapply H'4;
 [ intros H'5; try exact H'5; clear H'4 | clear H'4 ].
auto with algebra.
right; try assumption.
elim (H'0 x); intros H'3 H'4; lapply H'4;
 [ intros H'5; try exact H'5; clear H'4 | clear H'4 ].
auto with algebra.
Qed.

Lemma union_assoc :
 forall A B C : part_set E, Equal (union A (union B C)) (union (union A B) C).
unfold union in |- *; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros A B C x; split; [ try assumption | idtac ].
intuition.
intuition.
Qed.

Lemma union_com : forall A B : part_set E, Equal (union A B) (union B A).
unfold union in |- *; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros A B x; split; [ try assumption | idtac ].
intuition.
intuition.
Qed.
Parameter union_empty_l : forall A : part_set E, Equal (union (empty E) A) A.
Parameter union_empty_r : forall A : part_set E, Equal (union A (empty E)) A.
End Union1.
Hint Resolve included_union_l included_union_r in_part_union_l
  in_part_union_r included2_union union_comp union_assoc union_empty_l
  union_empty_r: algebra.
Hint Immediate union_com: algebra.