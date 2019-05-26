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
Require Export Parts2.
(** Title "Restrictions, inverse images." *)
Section Restrictions1.
Variable E F : Setoid.
Variable f : MAP E F.

Definition restrict : forall A : part_set E, MAP A F.
intros A; try assumption.
apply (Build_Map (Ap:=fun x : A => f (A x))).
red in |- *.
intros x y; try assumption.
elim y.
elim x.
simpl in |- *; auto with algebra.
Defined.

Lemma restrict_prop :
 forall (A : part_set E) (x : E) (p : in_part x A),
 Equal (restrict A (Build_subtype (subtype_elt:=x) p)) (f x).
simpl in |- *; auto with algebra.
Qed.

Lemma restrict_prop_in_part :
 forall (A : part_set E) (x : A), Equal (restrict A x) (f (A x)).
simpl in |- *; auto with algebra.
Qed.
End Restrictions1.
Hint Resolve restrict_prop: algebra.
Section Inverse_image1.
Variable E F : Setoid.
Section Inverse_image1_1.
Variable f : MAP E F.

Definition invimage : part_set F -> part_set E.
intros A.
apply (Build_Predicate (Pred_fun:=fun x : E => in_part (f x) A)).
red in |- *.
intros x y H' H'0; try assumption.
apply in_part_comp_l with (Ap f x); auto with algebra.
Defined.
End Inverse_image1_1.
Variable f : MAP E F.

Lemma invimage_in :
 forall (A : part_set F) (x : E), in_part x (invimage f A) -> in_part (f x) A.
simpl in |- *; auto with algebra.
Qed.

Lemma in_invimage :
 forall (A : part_set F) (x : E), in_part (f x) A -> in_part x (invimage f A).
simpl in |- *; auto with algebra.
Qed.
Hint Resolve in_invimage: algebra.

Lemma invimage_included :
 forall A B : part_set F,
 included A B -> included (invimage f A) (invimage f B).
unfold included in |- *.
simpl in |- *; auto with algebra.
Qed.
Hint Resolve invimage_included: algebra.

Lemma invimage_comp :
 forall A B : part_set F, Equal A B -> Equal (invimage f A) (invimage f B).
intros A B H'; try assumption.
apply included_antisym; auto with algebra.
Qed.
Hint Resolve invimage_comp: algebra.

Lemma invimage_image :
 forall A : part_set F, included (image f (invimage f A)) A.
unfold included in |- *.
simpl in |- *; auto with algebra.
intros A x H'; try assumption.
elim H'; intros x0 E0; elim E0; intros H'0 H'1; try exact H'1; clear E0 H'.
apply in_part_comp_l with (Ap f x0); auto with algebra.
Qed.

Lemma image_invimage :
 forall A : part_set E, included A (invimage f (image f A)).
unfold included in |- *.
simpl in |- *; auto with algebra.
intros A x H'; exists x; split; [ try assumption | idtac ]; auto with algebra.
Qed.
Hint Resolve invimage_image image_invimage: algebra.

Lemma invimage_image_invimage :
 forall A : part_set F,
 Equal (invimage f (image f (invimage f A))) (invimage f A).
simpl in |- *.
unfold eq_part in |- *.
intros A x; split; [ idtac | intros H'; try assumption ].
simpl in |- *.
intros H'; try assumption.
elim H'; intros x0 E0; elim E0; intros H'0 H'1; try exact H'0; clear E0 H'.
apply in_part_comp_l with (Ap f x0); auto with algebra.
auto with algebra.
Qed.

Lemma image_invimage_image :
 forall A : part_set E, Equal (image f (invimage f (image f A))) (image f A).
simpl in |- *.
unfold eq_part in |- *.
intros A x; split; [ try assumption | idtac ].
simpl in |- *; auto with algebra.
intros H'; try assumption.
elim H'; intros x0 E0; elim E0; intros H'0 H'1; elim H'0; intros x1 E1;
 elim E1; intros H'2 H'3; try exact H'2; clear E1 H'0 E0 H'.
exists x1; split; [ try assumption | idtac ]; auto with algebra.
apply Trans with (Ap f x0); auto with algebra.
simpl in |- *; auto with algebra.
intros H'; try assumption.
elim H'; intros x0 E0; elim E0; intros H'0 H'1; try exact H'0; clear E0 H'.
exists x0; split; [ exists x0; split; [ try assumption | idtac ] | idtac ];
 auto with algebra.
Qed.
End Inverse_image1.
Hint Resolve invimage_image_invimage image_invimage_image: algebra.
Hint Resolve in_invimage: algebra.
Hint Resolve invimage_included: algebra.
Hint Resolve invimage_comp: algebra.
