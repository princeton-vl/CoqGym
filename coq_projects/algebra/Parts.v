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
Require Export Sets.
(** Title "Parts of a set" *)
Comments
  "We define here the set of parts of a set, inclusion, union of a part,".
Comments
  "and we prove that there is no surjection from a set in its part set".
Section Subtype.
Comments "In Coq type theory, there is no primitive notion of subtype".
Comments "Then we have to define such a notion".
Variable E : Setoid.
Variable F : Type.
Variable i : F -> E.
Comments "We have implicitely defined a subset of" E "which is the image of"
  i ".".
Comments "As a setoid, this subset has" F
  " as carrier, and we identify two elements of" F
  "which have the same image by" i ":".

Definition subtype_image_equal (x y : F) : Prop := Equal (i x) (i y).

Lemma subtype_image_equiv : equivalence subtype_image_equal.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold subtype_image_equal in |- *; unfold app_rel in |- *; simpl in |- *;
 auto with algebra.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold subtype_image_equal in |- *; unfold app_rel in |- *; simpl in |- *;
 auto with algebra.
intros x y z H' H'0; try assumption.
apply Trans with (i y); auto with algebra.
red in |- *.
unfold subtype_image_equal in |- *; unfold app_rel in |- *; simpl in |- *;
 auto with algebra.
Qed.

Definition subtype_image_set : Setoid := Build_Setoid subtype_image_equiv.
End Subtype.
Section Part_type.
Comments "We define now a general structure for this kind of subset:".
Variable E : Setoid.

Record subtype_image : Type := 
  {subtype_image_carrier : Type;
   subtype_image_inj :> subtype_image_carrier -> E}.

Definition set_of_subtype_image (S : subtype_image) :=
  subtype_image_set (subtype_image_inj (s:=S)).
Comments "Parts of" E "will be nothing more than predicates on" E
  " which are compatible with equality:".

Definition pred_compatible (P : E -> Prop) : Prop :=
  forall x y : E, P x -> Equal y x -> (P y:Prop).

Record Predicate : Type := 
  {Pred_fun : E -> Prop; Pred_compatible_prf : pred_compatible Pred_fun:Prop}.
Variable P : Predicate.
Comments "The type of elements of the subset defined by" P
  "is the following:".

Record subtype : Type := 
  {subtype_elt : E; subtype_prf : Pred_fun P subtype_elt:Prop}.
Comments "Then elements of subsets are composed of an element of" E
  "and a proof that they verify the predicate" "given by" P.
Comments "We can now define the subset of" E "defined by the predicate" P ":".

Definition part :=
  Build_subtype_image (subtype_image_carrier:=subtype) subtype_elt.
End Part_type.
Comments "We can see a subset as a set with these coercions:".
Coercion set_of_subtype_image : subtype_image >-> Setoid.
Coercion part : Predicate >-> subtype_image.
Comments "We define" (in_part x A) "for elements of" E ":".

Definition in_part (E : Setoid) (x : E) (A : Predicate E) := Pred_fun A x.
Section Part_set.
Variable E : Setoid.
Comments "The equality between parts of" E ":".

Definition eq_part (A B : Predicate E) : Prop :=
  forall x : E, (in_part x A -> in_part x B) /\ (in_part x B -> in_part x A).

Let eq_part_equiv : equivalence eq_part.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold eq_part, app_rel in |- *; simpl in |- *.
intuition.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold eq_part, app_rel in |- *; simpl in |- *.
intros x y z H' H'0 x0; try assumption.
elim (H'0 x0); intros H'2 H'3; try exact H'2.
elim (H' x0); intros H'1 H'4; try exact H'1.
intuition.
red in |- *.
unfold eq_part, app_rel in |- *; simpl in |- *.
intros x y H' x0; try assumption.
elim (H' x0); intros H'2 H'3; try exact H'2.
intuition.
Qed.
Comments "We define the set" (part_set E) "of all parts of" E
  ", with its equality:".

Definition part_set : Setoid := Build_Setoid eq_part_equiv.
Comments "The empty part" (empty E) ":".
Hint Unfold pred_compatible: algebra.

Definition empty : part_set.
apply (Build_Predicate (E:=E) (Pred_fun:=fun x : E => False)).
auto with algebra.
Defined.
Comments "And the full part:".

Definition full : part_set.
apply (Build_Predicate (E:=E) (Pred_fun:=fun x : E => True)).
auto with algebra.
Defined.
End Part_set.
Hint Unfold pred_compatible: algebra.
Section Inclusion.
Variable E : Setoid.
Comments "The relation of belonging is compatible with equality:".

Lemma in_part_comp_l :
 forall (A : part_set E) (x y : E), in_part x A -> Equal y x -> in_part y A.
intros A; try assumption.
exact (Pred_compatible_prf (E:=E) (p:=A)).
Qed.

Lemma in_part_comp_r :
 forall (x : E) (A B : part_set E), in_part x A -> Equal A B -> in_part x B.
simpl in |- *; unfold eq_part in |- *.
intros x A B H' H'0; try assumption.
elim (H'0 x).
intuition.
Qed.

Lemma empty_prop : forall x : E, ~ in_part x (empty E).
unfold not in |- *; auto with algebra.
Qed.
Hint Resolve empty_prop: algebra.

Lemma full_prop : forall x : E, in_part x (full E).
unfold full in |- *; simpl in |- *; auto with algebra.
Qed.
Hint Resolve full_prop: algebra.

Definition full_to_set : MAP (full E) E.
apply (Build_Map (Ap:=fun x : full E => full E x)).
red in |- *.
intros x y; try assumption.
elim x.
elim y.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *; auto with algebra.
Defined.

Definition set_to_full : MAP E (full E).
apply
 (Build_Map (A:=E) (B:=full E)
    (Ap:=fun x : E =>
         Build_subtype (E:=E) (P:=full E) (subtype_elt:=x) (full_prop x))).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma set_full_set : Equal (comp_map_map full_to_set set_to_full) (Id E).
simpl in |- *; auto with algebra.
red in |- *.
simpl in |- *; auto with algebra.
Qed.

Lemma full_set_full :
 Equal (comp_map_map set_to_full full_to_set) (Id (full E)).
simpl in |- *; auto with algebra.
red in |- *.
simpl in |- *; auto with algebra.
intros x; try assumption.
elim x.
simpl in |- *; auto with algebra.
intros subtype_elt' subtype_prf'; red in |- *.
simpl in |- *; auto with algebra.
Qed.
Comments "The inclusion of parts:".

Definition included (A B : part_set E) : Prop :=
  forall x : E, in_part x A -> in_part x B.
Comments "The relation of inclusion is an order relation:".

Lemma included_refl : forall A : part_set E, included A A.
simpl in |- *; unfold included in |- *; auto with algebra.
Qed.
Hint Resolve included_refl: algebra.

Lemma included_antisym :
 forall A B : part_set E, included A B -> included B A -> Equal A B.
simpl in |- *; unfold eq_part, included in |- *; auto with algebra.
Qed.

Lemma included_trans :
 forall A B C : part_set E, included A B -> included B C -> included A C.
simpl in |- *; unfold included in |- *; auto with algebra.
Qed.
Comments "The inclusion relation is compatible with equality:".

Lemma included_comp :
 forall A A' B B' : part_set E,
 Equal A A' -> Equal B B' -> included A B -> included A' B'.
simpl in |- *; unfold eq_part, included in |- *.
intros A A' B B' H' H'0 H'1 x H'2; try assumption.
elim (H'0 x); intros H'4 H'5; apply H'4.
lapply (H'1 x); [ intros H'6; apply H'6 | idtac ].
elim (H' x); intros H'6 H'7; apply H'7; auto with algebra.
Qed.

Lemma eq_part_included : forall A B : part_set E, Equal A B -> included A B.
simpl in |- *; unfold eq_part, included in |- *.
intros A B H' x H'0; try assumption.
specialize  H' with (x := x); rename H' into H'1; try exact H'1.
elim H'1; intros H'2 H'3; try exact H'2; clear H'1; auto with algebra.
Qed.
Hint Resolve eq_part_included: algebra.

Lemma empty_included : forall A : part_set E, included (empty E) A.
simpl in |- *; unfold included in |- *; auto with algebra.
intros A x H'; try assumption.
absurd (in_part x (empty E)); auto with algebra.
Qed.

Lemma full_included : forall A : part_set E, included A (full E).
simpl in |- *; unfold included in |- *; auto with algebra.
Qed.
Hint Resolve empty_included full_included: algebra.

Definition inj_part : forall A : part_set E, MAP A E.
intros A; try assumption.
apply (Build_Map (Ap:=fun x : A => subtype_elt x)).
red in |- *.
auto with algebra.
Defined.

Lemma inj_part_injective : forall A : part_set E, injective (inj_part A).
intros A; try assumption.
red in |- *.
auto with algebra.
Qed.

Definition inj_part_included :
  forall A B : part_set E, included A B -> MAP A B.
intros A B H'; try assumption.
red in H'.
apply
 (Build_Map (A:=A) (B:=B)
    (Ap:=fun x : A => Build_subtype (H' (A x) (subtype_prf (E:=E) (P:=A) x)))).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Lemma inj_part_included_prop :
 forall (A B : part_set E) (p : included A B) (x : A),
 Equal (B (inj_part_included p x)) (A x).
simpl in |- *; auto with algebra.
Qed.

Lemma inj_part_included_injective :
 forall (A B : part_set E) (p : included A B),
 injective (inj_part_included p).
intros A B p; red in |- *.
intros x y; try assumption.
elim x.
elim y.
simpl in |- *; auto with algebra.
Qed.

Definition id_map_parts_equal : forall A B : part_set E, Equal A B -> MAP A B.
intros A B H'; try assumption.
exact (inj_part_included (eq_part_included H')).
Defined.

Lemma id_map_parts_equal_prop :
 forall (A B : part_set E) (p : Equal A B) (x : A),
 Equal (subtype_elt (id_map_parts_equal p x)) (subtype_elt x).
simpl in |- *; auto with algebra.
Qed.
End Inclusion.
Section Union_of_part.
Variable E : Setoid.
Comments "We define the union of a part of" (part_set E).
Variable P : part_set (part_set E).

Definition union_part : part_set E.
apply
 (Build_Predicate
    (Pred_fun:=fun x : E => exists A : part_set E, in_part A P /\ in_part x A)).
red in |- *.
intros x y H' H'0; try assumption.
elim H'; intros A E0; elim E0; clear H'.
intros H' H'1; try assumption.
exists A; split; [ try assumption | idtac ].
apply in_part_comp_l with x; auto with algebra.
Defined.

Lemma union_part_prop :
 forall x : E,
 in_part x union_part -> exists A : part_set E, in_part A P /\ in_part x A.
intros x H'; red in H'; auto with algebra.
Qed.

Lemma union_part_prop_rev :
 forall A : part_set E,
 in_part A P -> forall x : E, in_part x A -> in_part x union_part.
unfold union_part in |- *; simpl in |- *; auto with algebra.
intros A H' x H'0; try assumption.
exists A; split; [ try assumption | idtac ].
auto with algebra.
Qed.

Lemma union_part_included :
 forall A : part_set E, in_part A P -> included A union_part.
intros A H'; try assumption.
unfold included in |- *; auto with algebra.
intros x H'0; try assumption.
apply union_part_prop_rev with (A := A); auto with algebra.
Qed.

Lemma union_part_upper_bound :
 forall Y : part_set E,
 (forall A : part_set E, in_part A P -> included A Y) ->
 included union_part Y.
intros Y H'; try assumption.
unfold included in |- *.
intros x H'0; try assumption.
case (union_part_prop H'0).
intros A H'1; try assumption.
elim H'1.
intros H'2 H'3; try assumption.
unfold included in H'.
apply H' with (A := A); auto with algebra.
Qed.
End Union_of_part.
Section Part_set_greater.
Comments "A nice theorem:".
Variable E : Setoid.
Variable f : MAP E (part_set E).
Hypothesis fsurj : surjective f.

Let X_def (x : E) : Prop := ~ in_part x (f x).

Let X : part_set E.
apply (Build_Predicate (E:=E) (Pred_fun:=X_def)).
unfold X_def in |- *.
red in |- *.
unfold not in |- *.
intros x y H' H'0 H'1; try assumption.
apply H'.
apply in_part_comp_l with y; auto with algebra.
apply in_part_comp_r with (Ap f y); auto with algebra.
Defined.

Let invX : exists x : E, Equal X (f x).
exact (fsurj X).
Qed.

Lemma not_inpart_comp_r :
 forall (E : Setoid) (x : E) (A B : part_set E),
 ~ in_part x A -> Equal A B -> ~ in_part x B.
unfold not in |- *.
intros E0 x A B H' H'0 H'1; try assumption.
apply H'.
apply in_part_comp_r with B; auto with algebra.
Qed.

Theorem part_set_is_strictly_greater_than_set1 : False.
case invX.
intros x H'; try assumption.
cut (~ in_part x X).
intros H'0; try assumption.
absurd (in_part x X); auto with algebra.
simpl in |- *.
unfold X_def in |- *.
apply not_inpart_comp_r with X; auto with algebra.
unfold not in |- *.
intros H'0; try assumption.
absurd (in_part x X); auto with algebra.
apply not_inpart_comp_r with (Ap f x); auto with algebra.
Qed.
End Part_set_greater.

Theorem part_set_is_strictly_greater_than_set :
 forall (E : Setoid) (f : MAP E (part_set E)), ~ surjective f.
exact part_set_is_strictly_greater_than_set1.
Qed.
Hint Unfold pred_compatible: algebra.
Hint Resolve empty_prop full_prop included_refl eq_part_included
  empty_included full_included inj_part_injective inj_part_included_injective
  id_map_parts_equal_prop union_part_included union_part_upper_bound
  not_inpart_comp_r: algebra.