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
(** Title "Difference of two parts." *)
Section Diff.
Variable E : Setoid.

Definition diff : part_set E -> part_set E -> part_set E.
intros A B.
apply (Build_Predicate (Pred_fun:=fun x : E => in_part x A /\ ~ in_part x B)).
red in |- *.
intros x y H' H'0; try assumption.
elim H'; intros H'1 H'2; try exact H'1; clear H'.
split; [ try assumption | idtac ].
apply in_part_comp_l with x; auto with algebra.
red in |- *.
intros H'; try assumption.
absurd (in_part x B); auto with algebra.
apply in_part_comp_l with y; auto with algebra.
Defined.

Lemma diff_comp :
 forall A A' B B' : part_set E,
 Equal A A' -> Equal B B' -> Equal (diff A B) (diff A' B').
intros A A' B B'; try assumption.
unfold diff in |- *; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros H' H'0 x; split;
 [ intros H'1; split; [ try assumption | idtac ] | idtac ].
elim (H' x); intros H'3 H'4; lapply H'3;
 [ intros H'5; try exact H'5; clear H'3 | clear H'3 ].
elim H'1; intros H'2 H'3; try exact H'2; clear H'1.
red in |- *.
intros H'2; try assumption.
absurd (in_part x B); auto with algebra.
elim H'1; intros H'3 H'4; try exact H'4; clear H'1.
elim (H'0 x); intros H'4 H'5; lapply H'5;
 [ intros H'6; try exact H'6; clear H'5 | clear H'5 ].
auto with algebra.
intros H'1; split; [ try assumption | idtac ].
elim (H' x); intros H'3 H'4; lapply H'4;
 [ intros H'5; try exact H'5; clear H'4 | clear H'4 ].
elim H'1; intros H'2 H'4; try exact H'2; clear H'1.
red in |- *.
intros H'2; try assumption.
absurd (in_part x B'); auto with algebra.
elim H'1; intros H'3 H'4; try exact H'4; clear H'1.
elim (H'0 x); intros H'4 H'5; lapply H'4;
 [ intros H'6; try exact H'6; clear H'4 | clear H'4 ].
try exact H'2.
Qed.
End Diff.
Hint Resolve diff_comp: algebra.