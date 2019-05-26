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
Require Export Sgroup_facts.
Require Export Parts.
Section Def.
Variable G : SGROUP.
Section Sub_sgroup.
Variable H : part_set G.
Hypothesis
  Hprop :
    forall x y : G,
    in_part x H -> in_part y H -> in_part (sgroup_law _ x y) H.

Definition subsgroup_law : law_of_composition H.
unfold law_of_composition in |- *.
apply
 (Build_Map
    (A:=cart (set_of_subtype_image (part H)) (set_of_subtype_image (part H)))
    (B:=H)
    (Ap:=fun
           x : cart (set_of_subtype_image (part H))
                 (set_of_subtype_image (part H)) =>
         Build_subtype
           (Hprop (subtype_prf (proj1 x)) (subtype_prf (proj2 x))))).
red in |- *.
simpl in |- *.
unfold cart_eq, subtype_image_equal in |- *.
simpl in |- *.
unfold cart_eq, subtype_image_equal in |- *.
intuition.
Defined.

Definition subsgroup_sgroup : sgroup.
apply (Build_sgroup (sgroup_set:=H)).
apply (Build_sgroup_on (E:=H) (sgroup_law_map:=subsgroup_law)).
red in |- *.
simpl in |- *.
unfold subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.
End Sub_sgroup.

Record subsgroup : Type := 
  {subsgroup_part : Predicate G;
   subsgroup_prop :
    forall x y : G,
    in_part x subsgroup_part ->
    in_part y subsgroup_part -> in_part (sgroup_law _ x y) subsgroup_part}.

Definition sgroup_of_subsgroup (H : subsgroup) :=
  subsgroup_sgroup (subsgroup_prop (s:=H)).
End Def.
Coercion sgroup_of_subsgroup : subsgroup >-> sgroup.
Coercion subsgroup_part : subsgroup >-> Predicate.
Section Injection.
Variable G : SGROUP.
Variable H : subsgroup G.

Lemma subsgroup_in_prop :
 forall x y : G, in_part x H -> in_part y H -> in_part (sgroup_law _ x y) H.
intros x y H' H'0; try assumption.
apply (subsgroup_prop (G:=G) (s:=H)); auto with algebra.
Qed.

Definition inj_subsgroup : Hom (H:SGROUP) G.
apply (Build_sgroup_hom (E:=H) (F:=G) (sgroup_map:=inj_part H)).
red in |- *.
auto with algebra.
Defined.

Lemma inj_subgroup_injective : injective inj_subsgroup.
red in |- *.
auto with algebra.
Qed.
End Injection.
Hint Resolve subsgroup_in_prop inj_subgroup_injective: algebra.