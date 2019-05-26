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
(** Title "Singletons." *)
Section Single1.
Variable E : Setoid.

Definition single : E -> part_set E.
intros x.
apply (Build_Predicate (Pred_fun:=fun y : E => Equal y x)).
red in |- *.
intros x0 y H' H'0; try assumption.
apply Trans with x0; auto with algebra.
Defined.

Lemma in_single : forall x : E, in_part x (single x).
simpl in |- *; auto with algebra.
Qed.
Hint Resolve in_single: algebra.

Lemma single_law : forall x y : E, Equal x y -> Equal (single x) (single y).
unfold single in |- *; simpl in |- *.
unfold eq_part in |- *; simpl in |- *.
intros x y H' x0; split; [ intros H'0; try assumption | idtac ].
apply Trans with x; auto with algebra.
intros H'0; try assumption.
apply Trans with y; auto with algebra.
Qed.
Hint Resolve single_law: algebra.

Lemma single_prop : forall x y : E, Equal y x -> in_part y (single x).
simpl in |- *; auto with algebra.
Qed.
Hint Immediate single_prop: algebra.

Lemma single_prop_rev : forall x y : E, in_part y (single x) -> Equal y x.
simpl in |- *; auto with algebra.
Qed.
Hint Immediate single_prop_rev: algebra.

Lemma single_simpl : forall x y : E, Equal (single x) (single y) -> Equal x y.
simpl in |- *.
unfold eq_part, single in |- *; simpl in |- *.
intros x y H'; try assumption.
elim (H' x); auto with algebra.
Qed.
End Single1.
Hint Resolve single_law in_single: algebra.
Hint Immediate single_prop: algebra.
Hint Immediate single_prop_rev: algebra.
