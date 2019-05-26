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
Require Export Cartesian.
(** Title "Categories." *)
Comments "Some basic category theory.".
Section Category_def.
Section Category_def1.
Variable Ob : Type.
Variable Hom : Ob -> Ob -> Setoid.
Variable
  Hom_comp : forall a b c : Ob, MAP (cart (Hom b c) (Hom a b)) (Hom a c).
Variable Hom_id : forall a : Ob, Hom a a.

Definition Hom_comp_assoc :=
  forall (a b c d : Ob) (f : Hom a b) (g : Hom b c) (h : Hom c d),
  Equal (Hom_comp a b d (couple (Hom_comp b c d (couple h g)) f))
    (Hom_comp a c d (couple h (Hom_comp a b c (couple g f)))).

Definition Hom_comp_unit_l :=
  forall (a b : Ob) (f : Hom a b),
  Equal (Hom_comp a b b (couple (Hom_id b) f)) f.

Definition Hom_comp_unit_r :=
  forall (a b : Ob) (f : Hom a b),
  Equal (Hom_comp a a b (couple f (Hom_id a))) f.
End Category_def1.

Record category : Type := 
  {Ob :> Type;
   Hom : Ob -> Ob -> Setoid;
   Hom_comp : forall a b c : Ob, MAP (cart (Hom b c) (Hom a b)) (Hom a c);
   Hom_id : forall a : Ob, Hom a a;
   Hom_comp_assoc_prf : Hom_comp_assoc Hom_comp;
   Hom_comp_unit_l_prf : Hom_comp_unit_l Hom_comp Hom_id;
   Hom_comp_unit_r_prf : Hom_comp_unit_r Hom_comp Hom_id}.
Section Category_comp.
Variable C : category.

Definition comp_hom (a b c : C) (g : Hom b c) (f : Hom a b) :=
  Hom_comp a b c (couple g f).

Lemma comp_hom_compatible :
 forall (a b c : C) (x x' : Hom b c) (y y' : Hom a b),
 Equal x x' -> Equal y y' -> Equal (comp_hom x y) (comp_hom x' y').
intros a b c x x' y y' H' H'0; try assumption.
unfold comp_hom in |- *; auto with algebra.
Qed.

Lemma comp_hom_assoc :
 forall (a b c d : C) (f : Hom a b) (g : Hom b c) (h : Hom c d),
 Equal (comp_hom (comp_hom h g) f) (comp_hom h (comp_hom g f)).
exact (Hom_comp_assoc_prf (c:=C)).
Qed.

Lemma comp_hom_unit_l :
 forall (a b : C) (f : Hom a b), Equal (comp_hom (Hom_id b) f) f.
exact (Hom_comp_unit_l_prf (c:=C)).
Qed.

Lemma comp_hom_unit_r :
 forall (a b : C) (f : Hom a b), Equal (comp_hom f (Hom_id a)) f.
exact (Hom_comp_unit_r_prf (c:=C)).
Qed.
End Category_comp.
Hint Resolve comp_hom_compatible comp_hom_assoc comp_hom_unit_l
  comp_hom_unit_r: algebra.
Section Full_subcat_def.
Variable C : category.
Variable C' : Type.
Variable i : C' -> C.

Definition fsubcat_Hom (a b : C') := Hom (i a) (i b).

Definition fsubcat_Hom_comp :
  forall a b c : C',
  MAP (cart (fsubcat_Hom b c) (fsubcat_Hom a b)) (fsubcat_Hom a c).
intros a b c; try assumption.
exact (Hom_comp (i a) (i b) (i c)).
Defined.

Definition fsubcat_Hom_id (a : C') := Hom_id (i a).

Definition full_subcat : category.
apply
 (Build_category (Ob:=C') (Hom:=fsubcat_Hom) (Hom_comp:=fsubcat_Hom_comp)
    (Hom_id:=fsubcat_Hom_id)).
red in |- *.
unfold fsubcat_Hom, fsubcat_Hom_comp in |- *; simpl in |- *.
intros a b c d f g h; try assumption.
apply (Hom_comp_assoc_prf (c:=C)).
red in |- *.
unfold fsubcat_Hom, fsubcat_Hom_comp, fsubcat_Hom_id in |- *; simpl in |- *.
intros a b f; try assumption.
apply (Hom_comp_unit_l_prf (c:=C)).
red in |- *.
unfold fsubcat_Hom, fsubcat_Hom_comp, fsubcat_Hom_id in |- *; simpl in |- *.
intros a b f; try assumption.
apply (Hom_comp_unit_r_prf (c:=C)).
Defined.
End Full_subcat_def.
End Category_def.
Hint Resolve comp_hom_compatible comp_hom_assoc comp_hom_unit_l
  comp_hom_unit_r: algebra.