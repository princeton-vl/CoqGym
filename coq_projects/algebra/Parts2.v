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
Require Export Classical_Prop.
Require Export Parts.
(** Title "Complement, images." *)
Comments "We define here complement of a part, image of a part by a map.".
Section Complement1.
Variable E : Setoid.

Lemma not_in_comp_l :
 forall (E : Setoid) (A : part_set E) (x y : E),
 ~ in_part x A -> Equal y x -> ~ in_part y A.
unfold not in |- *.
intros E0 A x y H' H'0 H'1; try assumption.
apply H'.
apply in_part_comp_l with y; auto with algebra.
Qed.

Lemma not_in_comp_r :
 forall (E : Setoid) (A B : part_set E) (x : E),
 ~ in_part x A -> Equal A B -> ~ in_part x B.
unfold not in |- *.
intros E0 A B x H' H'0 H'1; try assumption.
apply H'.
apply in_part_comp_r with B; auto with algebra.
Qed.

Definition compl : part_set E -> part_set E.
intros A.
apply (Build_Predicate (Pred_fun:=fun x : E => ~ in_part x A)).
red in |- *.
intros x y H' H'0; try assumption.
apply not_in_comp_l with x; auto with algebra.
Defined.

Lemma compl_in :
 forall (A : part_set E) (x : E), ~ in_part x A -> in_part x (compl A).
simpl in |- *; auto with algebra.
Qed.
Hint Resolve compl_in: algebra.

Lemma in_compl :
 forall (A : part_set E) (x : E), in_part x (compl A) -> ~ in_part x A.
simpl in |- *; auto with algebra.
Qed.

Lemma compl_comp :
 forall A B : part_set E, Equal A B -> Equal (compl A) (compl B).
simpl in |- *; auto with algebra.
unfold eq_part in |- *; auto with algebra.
intros A B H' x; try assumption.
elim (H' x).
simpl in |- *; unfold not in |- *.
intuition.
Qed.
Hint Resolve compl_comp: algebra.

Lemma compl_comp_rev :
 forall A B : part_set E, Equal (compl A) (compl B) -> Equal A B.
simpl in |- *; auto with algebra.
unfold eq_part in |- *; auto with algebra.
simpl in |- *; unfold not in |- *.
intros A B H' x; try assumption.
elim (H' x).
apply NNPP.
tauto.
Qed.

Lemma compl_compl : forall A : part_set E, Equal (compl (compl A)) A.
simpl in |- *; auto with algebra.
unfold eq_part in |- *; auto with algebra.
simpl in |- *; unfold not in |- *.
intros A x; try assumption.
split; [ try assumption | idtac ].
apply NNPP.
tauto.
Qed.
Hint Resolve compl_compl: algebra.

Lemma compl_not_in :
 forall (A : part_set E) (x : E), in_part x A -> ~ in_part x (compl A).
simpl in |- *; auto with algebra.
Qed.
Hint Resolve compl_not_in: algebra.

Lemma not_in_compl :
 forall (A : part_set E) (x : E), in_part x (compl A) -> ~ in_part x A.
simpl in |- *; auto with algebra.
Qed.

Lemma compl_included :
 forall A B : part_set E, included A B -> included (compl B) (compl A).
unfold included in |- *.
simpl in |- *; auto with algebra.
Qed.

Lemma compl_not_compl :
 forall (A : part_set E) (x : E), in_part x A \/ in_part x (compl A).
intros A x; try assumption.
simpl in |- *.
unfold not in |- *.
apply NNPP; intuition.
Qed.
End Complement1.
Hint Resolve compl_included compl_not_in compl_compl compl_comp compl_in:
  algebra.
Section Images1.
Variable E F : Setoid.
Variable f : MAP E F.

Definition image : part_set E -> part_set F.
intros A.
apply
 (Build_Predicate
    (Pred_fun:=fun y : F => exists x : E, in_part x A /\ Equal y (f x))).
red in |- *.
intros y y' H' H'0; try assumption.
elim H'; intros x E0; elim E0; intros H'1 H'2; try exact H'1; clear E0 H'.
exists x; split; [ try assumption | idtac ].
apply Trans with y; auto with algebra.
Defined.

Lemma image_in :
 forall (A : part_set E) (y : F),
 in_part y (image A) -> exists x : E, in_part x A /\ Equal y (f x).
simpl in |- *; auto with algebra.
Qed.

Lemma in_image :
 forall (A : part_set E) (x : E) (y : F),
 in_part x A -> Equal y (f x) -> in_part y (image A).
simpl in |- *; auto with algebra.
intros A x y H' H'0; try assumption.
exists x; split; [ try assumption | idtac ]; auto with algebra.
Qed.
Hint Resolve in_image: algebra.

Lemma image_included :
 forall A B : part_set E, included A B -> included (image A) (image B).
intros A B H'; try assumption.
unfold included in |- *.
intros x H'0; try assumption.
elim H'0.
intros x0 H'1; try assumption.
apply in_image with (x := x0); auto with algebra.
red in H'.
elim H'1.
auto with algebra.
elim H'1; auto with algebra.
Qed.
Hint Resolve image_included: algebra.

Lemma image_comp :
 forall A B : part_set E, Equal A B -> Equal (image A) (image B).
intros A B H'; try assumption.
apply included_antisym; auto with algebra.
Qed.
Hint Resolve image_comp: algebra.

Lemma image_in_image :
 forall (A : part_set E) (x : E), in_part x A -> in_part (f x) (image A).
simpl in |- *; auto with algebra.
intros A x H'; try assumption.
exists x; split; [ try assumption | idtac ]; auto with algebra.
Qed.
Hint Resolve image_in_image: algebra.

Definition image_map := image (full E).

Let surj_set_image_fun : E -> image_map.
intros x; try assumption.
unfold image_map in |- *.
simpl in |- *.
cut (in_part (f x) (image (full E))).
intros H'; try assumption.
apply (Build_subtype (P:=image (full E)) (subtype_elt:=f x) H').
auto with algebra.
Defined.

Definition surj_set_image : MAP E image_map.
apply (Build_Map (Ap:=surj_set_image_fun)).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.

Lemma surj_set_image_surjective : surjective surj_set_image.
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
unfold image_map in |- *.
intros y; try assumption.
elim y.
intros x' subtype_prf; try assumption.
elim subtype_prf.
intros x H'; try assumption.
exists x; try assumption.
elim H'; intros H'0 H'1; try exact H'1; clear H'.
Qed.

Let surj_part_image_fun : forall A : part_set E, A -> image A.
intros A x; try assumption.
elim x.
intros x' H'; try assumption.
cut (in_part (f x') (image A)).
intros H'0; try assumption.
simpl in |- *.
apply (Build_subtype (P:=image A) (subtype_elt:=f x') H'0).
auto with algebra.
Defined.

Definition surj_part_image : forall A : part_set E, MAP A (image A).
intros A; try assumption.
apply (Build_Map (Ap:=surj_part_image_fun (A:=A))).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
intros x y; try assumption.
elim x.
elim y.
simpl in |- *.
auto with algebra.
Defined.

Lemma surj_part_image_surjective :
 forall A : part_set E, surjective (surj_part_image A).
red in |- *.
intros A y; try assumption.
case (image_in (subtype_prf y)).
intros x H'; try assumption.
elim H'; intros H'0 H'1; try exact H'1; clear H'.
exists (Build_subtype H'0); try assumption.
Qed.
End Images1.
Hint Resolve in_image image_included image_comp image_in_image
  surj_set_image_surjective surj_part_image_surjective: algebra.













