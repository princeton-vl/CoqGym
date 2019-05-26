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
Require Export Categories.
Require Export Parts.
(** Title "Sub-category." *)
Section Subcategory_def.
Variable C : category.
Variable C' : Type.
Variable i : C' -> C.
Variable homC' : forall a b : C', subtype_image (Hom (i a) (i b)).

Definition subcat_Hom (a b : C') := homC' a b:Setoid.
Variable
  CompC' :
    forall a b c : C', subcat_Hom b c -> subcat_Hom a b -> subcat_Hom a c.
Variable idC' : forall a : C', subcat_Hom a a.
Hypothesis
  idC'ok : forall a : C', Equal (subtype_image_inj (idC' a)) (Hom_id (i a)).
Hypothesis
  CompC'_ok :
    forall (a b c : C') (g : subcat_Hom b c) (f : subcat_Hom a b),
    Equal (subtype_image_inj (CompC' g f))
      (comp_hom (subtype_image_inj g) (subtype_image_inj f)).

Definition subcat_Hom_comp :
  forall a b c : C',
  MAP (cart (subcat_Hom b c) (subcat_Hom a b)) (subcat_Hom a c).
intros a b c; try assumption.
apply
 (Build_Map (A:=cart (subcat_Hom b c) (subcat_Hom a b)) (B:=
    subcat_Hom a c)
    (Ap:=fun x : cart (subcat_Hom b c) (subcat_Hom a b) =>
         CompC' (proj1 x) (proj2 x))).
red in |- *.
intros x y H'; try assumption.
simpl in |- *.
unfold subtype_image_equal in |- *.
apply
 Trans
  with (comp_hom (subtype_image_inj (proj1 x)) (subtype_image_inj (proj2 x)));
 auto with algebra.
apply
 Trans
  with (comp_hom (subtype_image_inj (proj1 y)) (subtype_image_inj (proj2 y)));
 auto with algebra.
apply comp_hom_compatible.
cut (Equal (proj1 x) (proj1 y)).
auto with algebra.
auto with algebra.
cut (Equal (proj2 x) (proj2 y)).
auto with algebra.
auto with algebra.
Defined.

Definition subcat : category.
apply
 (Build_category (Ob:=C') (Hom:=subcat_Hom) (Hom_comp:=subcat_Hom_comp)
    (Hom_id:=idC')).
red in |- *.
unfold subcat_Hom_comp in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
intros a b c d f g h; try assumption.
apply
 Trans with (comp_hom (subtype_image_inj (CompC' h g)) (subtype_image_inj f));
 auto with algebra.
apply
 Trans
  with
    (comp_hom (comp_hom (subtype_image_inj h) (subtype_image_inj g))
       (subtype_image_inj f)); auto with algebra.
apply
 Trans with (comp_hom (subtype_image_inj h) (subtype_image_inj (CompC' g f)));
 auto with algebra.
apply
 Trans
  with
    (comp_hom (subtype_image_inj h)
       (comp_hom (subtype_image_inj g) (subtype_image_inj f)));
 auto with algebra.
red in |- *.
unfold subcat_Hom_comp in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
intros a b f; try assumption.
apply
 Trans with (comp_hom (subtype_image_inj (idC' b)) (subtype_image_inj f));
 auto with algebra.
apply Trans with (comp_hom (Hom_id (i b)) (subtype_image_inj f));
 auto with algebra.
red in |- *.
unfold subcat_Hom_comp in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
intros a b f; try assumption.
apply
 Trans with (comp_hom (subtype_image_inj f) (subtype_image_inj (idC' a)));
 auto with algebra.
apply Trans with (comp_hom (subtype_image_inj f) (Hom_id (i a)));
 auto with algebra.
Defined.
End Subcategory_def.