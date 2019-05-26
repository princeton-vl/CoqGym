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


Global Set Automatic Coercions Import.
Global Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.
(** Title "Sets, relations, maps" *)
Section Sets1.
Comments
  "Basically, algebraic structures are sets, in which we talk about elements, belonging, equality,"
  "applications, equivalence relations, quotient sets, etc".
Comments
  "Types in Coq are not well-suited to represent sets, because they cannot be quotiented".
Comments "We will define sets in Coq as types with an equivalence relation".
Comments "First, we need some definitions on binary relations on types:".
Section Relations.
Variable E : Type.

Definition relation (E : Type) := E -> E -> Prop.

Definition app_rel (R : relation E) (x y : E) := R x y.

Definition reflexive (R : relation E) : Prop := forall x : E, app_rel R x x.

Definition symmetric (R : relation E) : Prop :=
  forall x y : E, app_rel R x y -> app_rel R y x.

Definition transitive (R : relation E) : Prop :=
  forall x y z : E, app_rel R x y -> app_rel R y z -> app_rel R x z.
Comments "A partial equivalence on" E
  " is a relation which is transitive and symmetric:".

Definition partial_equivalence (R : relation E) : Prop :=
  transitive R /\ symmetric R.
Comments "An equivalence relation is reflexive, symmetric and transitive:".

Definition equivalence (R : relation E) : Prop :=
  reflexive R /\ partial_equivalence R.
Comments "Some immediate properties:".

Lemma equiv_refl : forall R : relation E, equivalence R -> reflexive R.
compute in |- *. tauto.
Qed.

Lemma equiv_sym : forall R : relation E, equivalence R -> symmetric R.
compute in |- *; tauto.
Qed.

Lemma equiv_trans : forall R : relation E, equivalence R -> transitive R.
compute in |- *; tauto.
Qed.
End Relations.
Hint Unfold reflexive transitive symmetric partial_equivalence equivalence:
  algebra.
Hint Resolve equiv_refl equiv_sym equiv_trans: algebra.
Comments "Then we define a dedicated structure to represent sets:".

Record Setoid : Type := 
  {Carrier :> Type; Equal : relation Carrier; Prf_equiv :> equivalence Equal}.
Hint Resolve Prf_equiv: algebra.
Comments
  "A set is then given by a type (for its elements), a binary relation"
  "and a proof that this relation is an equivalence relation".
Comments "We will write" (Equal x y)
  "for the equality of two elements of a set".

Lemma Refl : forall (E : Setoid) (x : E), Equal x x.
intros E; try assumption.
cut (reflexive (Equal (s:=E))); auto with algebra.
Qed.

Lemma Sym : forall (E : Setoid) (x y : E), Equal x y -> Equal y x.
intros E; try assumption.
cut (symmetric (Equal (s:=E))); auto with algebra.
Qed.

Lemma Trans :
 forall (E : Setoid) (x y z : E), Equal x y -> Equal y z -> Equal x z.
intros E; try assumption.
cut (transitive (Equal (s:=E))); auto with algebra.
Qed.
Hint Resolve Refl: algebra.
Hint Immediate Sym: algebra.
Comments
  "Every type in Coq can be seen as a set, with the Leibnitz equality:".

Let eqT_equiv : forall A : Type, equivalence (eq (A:=A)).
intros A; try assumption.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold app_rel in |- *; auto with algebra.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold app_rel in |- *; auto with algebra.
intros x y z H' H'0; try assumption.
rewrite H'; auto with algebra.
red in |- *.
unfold app_rel in |- *; auto with algebra.
Qed.

Definition Leibnitz_set (A : Type) : Setoid := Build_Setoid (eqT_equiv A).

Lemma Leibnitz_set_prop :
 forall (A : Type) (x y : Leibnitz_set A), Equal x y -> x = y.
auto with algebra.
Qed.

Lemma Leibnitz_set_prop_rev :
 forall (A : Type) (x y : Leibnitz_set A), x = y -> Equal x y.
auto with algebra.
Qed.
Section Quotient1.
Comments
  "We can now define quotient sets, using equivalence relations on sets".
Comments
  "A binary relation on a set is a binary relation on its carrier, which is compatible with equality:".
Variable E : Setoid.

Definition rel_compatible (R : relation E) : Prop :=
  forall x x' y y' : E,
  Equal x x' -> Equal y y' -> app_rel R x y -> app_rel R x' y'.

Record Relation : Type := 
  {Rel_fun :> relation E; Rel_compatible_prf : rel_compatible Rel_fun}.

Lemma Rel_comp :
 forall (R : Relation) (x x' y y' : E),
 Equal x x' -> Equal y y' -> app_rel R x y -> app_rel R x' y'.
intros R; try assumption.
exact (Rel_compatible_prf (r:=R)).
Qed.
Hint Resolve Rel_comp: algebra.
Variable R : Relation.
Hypothesis R_equiv : equivalence R.
Set Strict Implicit.
Unset Implicit Arguments.

Definition quotient : Setoid := Build_Setoid R_equiv.
Set Implicit Arguments.
Unset Strict Implicit.
End Quotient1.
Section Maps1.
Comments
  "Maps between two sets are functions which are compatible with equalities:".
Section Maps1_1.
Variable A B : Setoid.

Definition fun_compatible (f : A -> B) : Prop :=
  forall x y : A, Equal x y -> Equal (f x) (f y).

Record Map : Type := 
  {Ap :> A -> B; Map_compatible_prf :> fun_compatible Ap:Prop}.
Comments "Two maps are equal when they have the same values:".

Definition Map_eq (f g : Map) : Prop := forall x : A, Equal (f x) (g x).

Let Map_eq_equiv : equivalence Map_eq.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold Map_eq, app_rel in |- *; simpl in |- *; auto with algebra.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
unfold Map_eq, app_rel in |- *; simpl in |- *; auto with algebra.
intros x y z H' H'0 x0; try assumption.
apply Trans with (y x0); auto with algebra.
red in |- *.
unfold Map_eq, app_rel in |- *; simpl in |- *; auto with algebra.
Qed.

Definition MAP : Setoid := Build_Setoid Map_eq_equiv.
Comments "We note" (MAP A B) "the set of maps between" A "and" B.
End Maps1_1.
Comments "Some immediate properties of maps:".

Lemma Ap_comp :
 forall (A B : Setoid) (f g : MAP A B) (x y : A),
 Equal x y -> Equal f g -> Equal (f x) (g y).
intros A B f g x y H' H'0; try assumption.
apply Trans with (f y).
apply (Map_compatible_prf f); auto with algebra.
simpl in H'0.
unfold Map_eq in H'0.
auto with algebra.
Qed.
Hint Resolve Ap_comp: algebra.

Lemma map_ext :
 forall (A B : Setoid) (f g : MAP A B),
 (forall x : A, Equal (f x) (g x)) -> Equal f g.
simpl in |- *.
unfold Map_eq in |- *.
auto with algebra.
Qed.
Hint Resolve map_ext: algebra.
Section Maps1_2.
Comments "We define now injections, surjections and bijections.".
Variable A B : Setoid.

Definition injective (f : MAP A B) : Prop :=
  forall x y : A, Equal (f x) (f y) -> Equal x y.

Definition surjective (f : MAP A B) : Prop :=
  forall y : B, exists x : A, Equal y (f x).

Definition bijective (f : MAP A B) : Prop := injective f /\ surjective f.
End Maps1_2.
Comments "These definitions are coherent with equality of maps:".

Lemma injective_comp :
 forall (A B : Setoid) (f f' : MAP A B),
 injective f -> Equal f f' -> injective f'.
unfold injective in |- *.
intros A B f f' H' H'0 x y H'1; try assumption.
apply H'.
apply Trans with (Ap f' x); auto with algebra.
apply Trans with (Ap f' y); auto with algebra.
Qed.

Lemma surjective_comp :
 forall (A B : Setoid) (f f' : MAP A B),
 surjective f -> Equal f f' -> surjective f'.
unfold surjective in |- *.
intros A B f f' H' H'0 y; try assumption.
elim (H' y); intros x E; try exact E.
exists x; try assumption.
apply Trans with (Ap f x); auto with algebra.
Qed.

Lemma bijective_comp :
 forall (A B : Setoid) (f f' : MAP A B),
 bijective f -> Equal f f' -> bijective f'.
unfold bijective in |- *.
intros A B f f' H' H'0; try assumption.
split; [ try assumption | idtac ].
elim H'; intros H'1 H'2; try exact H'1; clear H'.
apply injective_comp with (f := f); auto with algebra.
elim H'; intros H'1 H'2; try exact H'2; clear H'.
apply surjective_comp with (f := f); auto with algebra.
Qed.
Comments "Trivialities:".

Lemma bijective_injective :
 forall (A B : Setoid) (f : MAP A B), bijective f -> injective f.
intros A B f H'; red in H'; auto with algebra.
elim H'; auto with algebra.
Qed.
Hint Resolve bijective_injective: algebra.

Lemma bijective_surjective :
 forall (A B : Setoid) (f : MAP A B), bijective f -> surjective f.
intros A B f H'; red in H'; auto with algebra.
elim H'; auto with algebra.
Qed.
Hint Resolve bijective_surjective: algebra.
Set Strict Implicit.
Unset Implicit Arguments.

Definition surj_set_quo :
  forall (E : Setoid) (R : Relation E) (p : equivalence R),
  MAP E (quotient E R p).
intros E R p; try assumption.
apply (Build_Map (A:=E) (B:=quotient E R p) (Ap:=fun x : E => x)).
generalize p; clear p.
elim R.
intros Rel_fun' Rel_compatible_prf0 p; try assumption.
red in |- *.
red in Rel_compatible_prf0.
intros x y H'; try assumption.
simpl in |- *.
unfold app_rel in Rel_compatible_prf0.
apply Rel_compatible_prf0 with (x := x) (y := x); auto with algebra.
elim p.
intros H'0 H'1; try assumption.
simpl in H'0.
red in H'0.
unfold app_rel in H'0.
auto with algebra.
Defined.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma surj_set_quo_surjective :
 forall (E : Setoid) (R : Relation E) (p : equivalence R),
 surjective (surj_set_quo E R p).
intros E R p; try assumption.
red in |- *.
intros y; exists y; try assumption.
simpl in |- *.
elim p.
intros H'; red in H'.
unfold app_rel in H'.
auto with algebra.
Qed.
Section Maps1_3.
Comments "We define the composition of maps:".
Variable E F G : Setoid.
Variable g : MAP F G.
Variable f : MAP E F.
Comments
  "First, we define the composition of the functions associated to two maps:"
  f "and" g.

Definition comp_map_fun (x : E) := g (f x).
Comments "Then, we proof that the result is compatible with equality:".

Lemma comp_map_fun_compatible : fun_compatible comp_map_fun.
red in |- *.
unfold comp_map_fun in |- *.
auto with algebra.
Qed.
Comments "With this result, we can build the composed map:".

Definition comp_map_map : MAP E G := Build_Map comp_map_fun_compatible.
End Maps1_3.
Comments "We note" (comp_map_map g f) "the composition of" g "and" f.
Comments "Composition is compatible with equality of maps:".

Lemma comp_map_comp :
 forall (A B C : Setoid) (f f' : MAP A B) (g g' : MAP B C),
 Equal f f' -> Equal g g' -> Equal (comp_map_map g f) (comp_map_map g' f').
unfold comp_map_map in |- *; simpl in |- *.
unfold Map_eq in |- *; simpl in |- *; auto with algebra.
unfold comp_map_fun in |- *.
auto with algebra.
Qed.
Hint Resolve comp_map_comp: algebra.
Comments "Composition is associative:".

Lemma comp_map_assoc :
 forall (A B C D : Setoid) (f : MAP A B) (g : MAP B C) (h : MAP C D),
 Equal (comp_map_map h (comp_map_map g f))
   (comp_map_map (comp_map_map h g) f).
unfold comp_map_map in |- *; simpl in |- *.
unfold Map_eq in |- *; simpl in |- *; auto with algebra.
Qed.
Hint Resolve comp_map_assoc: algebra.
Comments "We define now the identity map:".

Definition Id : forall A : Setoid, MAP A A.
intros A; try assumption.
apply (Build_Map (A:=A) (B:=A) (Ap:=fun x : A => x)).
red in |- *.
auto with algebra.
Defined.
Comments "Identity map is a unit element for composition:".

Lemma Id_unit_r :
 forall (A B : Setoid) (f : MAP A B), Equal (comp_map_map f (Id A)) f.
unfold comp_map_map in |- *; simpl in |- *.
unfold Map_eq in |- *; simpl in |- *; auto with algebra.
Qed.
Hint Resolve Id_unit_r: algebra.

Lemma Id_unit_l :
 forall (A B : Setoid) (f : MAP A B), Equal (comp_map_map (Id B) f) f.
unfold comp_map_map in |- *; simpl in |- *.
unfold Map_eq in |- *; simpl in |- *; auto with algebra.
Qed.
Hint Resolve Id_unit_l: algebra.

Lemma Id_is_bijective : forall A : Setoid, bijective (Id A).
intros A; red in |- *.
split; [ red in |- * | idtac ].
simpl in |- *; auto with algebra.
red in |- *.
intros y; exists y; try assumption; auto with algebra.
Qed.
Hint Resolve Id_is_bijective: algebra.
Comments "Some properties of composition:".

Lemma comp_injective :
 forall (A B C : Setoid) (f : MAP A B) (g : MAP B C),
 injective (comp_map_map g f) -> injective f.
unfold injective in |- *.
intros A B C f g H' x y H'0; try assumption.
apply H'.
unfold comp_map_map in |- *; simpl in |- *.
unfold comp_map_fun in |- *.
auto with algebra.
Qed.
Hint Resolve comp_injective: algebra.

Lemma comp_surjective :
 forall (A B C : Setoid) (f : MAP A B) (g : MAP B C),
 surjective (comp_map_map g f) -> surjective g.
unfold surjective in |- *.
intros A B C f g H' y; try assumption.
elim (H' y); intros x E; try exact E.
simpl in E.
unfold comp_map_fun in E.
exists (Ap f x); try assumption; auto with algebra.
Qed.

Lemma comp_is_id_then_bijective :
 forall (A B : Setoid) (f : MAP A B) (g : MAP B A),
 Equal (comp_map_map g f) (Id A) ->
 Equal (comp_map_map f g) (Id B) -> bijective f.
intros A B f g H' H'0; try assumption.
unfold bijective in |- *.
split; [ try assumption | idtac ].
apply comp_injective with A g; auto with algebra.
apply injective_comp with (f := Id A); auto with algebra.
apply comp_surjective with B g; auto with algebra.
apply surjective_comp with (f := Id B); auto with algebra.
Qed.

Lemma comp_is_id_then_injective :
 forall (A B : Setoid) (f : MAP A B) (g : MAP B A),
 Equal (comp_map_map g f) (Id A) -> injective f.
intros A B f g H'; try assumption.
apply comp_injective with A g; auto with algebra.
apply injective_comp with (f := Id A); auto with algebra.
Qed.

Lemma comp_is_id_then_surjective :
 forall (A B : Setoid) (f : MAP A B) (g : MAP B A),
 Equal (comp_map_map f g) (Id B) -> surjective f.
intros A B f g H'; try assumption.
apply comp_surjective with B g; auto with algebra.
apply surjective_comp with (f := Id B); auto with algebra.
Qed.
End Maps1.
End Sets1.
Hint Immediate Sym: algebra.
Hint Unfold reflexive transitive symmetric partial_equivalence equivalence:
  algebra.
Hint Resolve equiv_refl equiv_sym equiv_trans Prf_equiv Refl Rel_comp Ap_comp
  map_ext bijective_injective bijective_surjective surj_set_quo_surjective
  comp_map_comp comp_map_assoc Id_unit_r Id_unit_l Id_is_bijective
  comp_injective: algebra.
