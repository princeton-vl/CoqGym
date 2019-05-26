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
Require Export Subcat.
Require Export Set_cat.
(** Title "The category of semi-groups." *)

Definition law_of_composition (E : SET) := Hom (cart E E:SET) E.

Definition associative (E : SET) (f : law_of_composition E) :=
  forall x y z : E,
  Equal (f (couple (f (couple x y)) z)) (f (couple x (f (couple y z)))).

Record sgroup_on (E : SET) : Type := 
  {sgroup_law_map : law_of_composition E;
   sgroup_assoc_prf : associative sgroup_law_map}.

Record sgroup : Type := 
  {sgroup_set :> Setoid; sgroup_on_def :> sgroup_on sgroup_set}.
Coercion Build_sgroup : sgroup_on >-> sgroup.
Set Strict Implicit.
Unset Implicit Arguments.

Definition sgroup_law (E : sgroup) : E -> E -> E :=
  fun x y : E:Setoid => sgroup_law_map E (couple x y).
Set Implicit Arguments.
Unset Strict Implicit.
Section Hom.
Variable E F : sgroup.

Definition sgroup_hom_prop (f : Hom (E:SET) F) :=
  forall x y : E, Equal (f (sgroup_law _ x y)) (sgroup_law _ (f x) (f y)).

Record sgroup_hom : Type := 
  {sgroup_map :> Map E F; sgroup_hom_prf : sgroup_hom_prop sgroup_map}.
End Hom.

Definition sgroup_hom_comp :
  forall E F G : sgroup, sgroup_hom F G -> sgroup_hom E F -> sgroup_hom E G.
intros E F G g f; try assumption.
apply (Build_sgroup_hom (sgroup_map:=comp_map_map g f)).
unfold sgroup_hom_prop in |- *; auto with algebra.
simpl in |- *.
unfold comp_map_fun in |- *.
intros x y; try assumption.
apply
 Trans
  with
    (Ap (sgroup_map g)
       (sgroup_law _ (Ap (sgroup_map f) x) (Ap (sgroup_map f) y)));
 auto with algebra.
cut
 (Equal (Ap (sgroup_map f) (sgroup_law _ x y))
    (sgroup_law _ (Ap (sgroup_map f) x) (Ap (sgroup_map f) y))).
auto with algebra.
apply (sgroup_hom_prf f).
apply (sgroup_hom_prf g).
Defined.

Definition sgroup_id : forall E : sgroup, sgroup_hom E E.
intros E; try assumption.
apply (Build_sgroup_hom (sgroup_map:=Id E)).
red in |- *.
simpl in |- *; auto with algebra.
Defined.

Definition SGROUP : category.
apply
 (subcat (C:=SET) (C':=sgroup) (i:=sgroup_set)
    (homC':=fun E F : sgroup =>
            Build_subtype_image (E:=MAP E F)
              (subtype_image_carrier:=sgroup_hom E F)
              (sgroup_map (E:=E) (F:=F))) (CompC':=sgroup_hom_comp)
    (idC':=sgroup_id)).
simpl in |- *.
intros a; try assumption.
red in |- *.
auto with algebra.
simpl in |- *.
intros a b c g f; try assumption.
red in |- *.
auto with algebra.
Defined.