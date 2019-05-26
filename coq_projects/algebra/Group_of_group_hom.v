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
Require Export Group_util.
Require Export Abelian_group_facts.
(** Title "The abelian group of morphisms from a group to an abelian group." *)
Section Def.
Variable G : GROUP.
Variable G' : ABELIAN_GROUP.

Definition group_hom_law : forall f g : Hom G G', Hom G G'.
intros f0 g.
apply
 (BUILD_HOM_GROUP (G:=G) (G':=G')
    (ff:=fun x : G => sgroup_law G' (f0 x) (g x))).
auto with algebra.
intros x y; try assumption.
apply
 Trans
  with
    (sgroup_law G'
       (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom f0)) x)
          (Ap (sgroup_map (monoid_sgroup_hom f0)) y))
       (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom g)) x)
          (Ap (sgroup_map (monoid_sgroup_hom g)) y))); 
 auto with algebra.

apply Trans with (sgroup_law G' (monoid_unit G') (monoid_unit G'));
 auto with algebra.
Defined.

Definition group_hom_unit : Hom G G'.
apply (BUILD_HOM_GROUP (G:=G) (G':=G') (ff:=fun x : G => monoid_unit G')).
auto with algebra.
auto with algebra.
auto with algebra.
Defined.

Definition group_hom_inv : forall f : Hom G G', Hom G G'.
intros f0.
apply
 (BUILD_HOM_GROUP (G:=G) (G':=G') (ff:=fun x : G => group_inverse G' (f0 x))).
auto with algebra.
intros x y; try assumption.
apply
 Trans
  with
    (Ap (sgroup_map (monoid_sgroup_hom f0))
       (group_inverse G (sgroup_law G x y))); auto with algebra.
apply
 Trans
  with
    (Ap (sgroup_map (monoid_sgroup_hom f0))
       (sgroup_law G (group_inverse G y) (group_inverse G x)));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G'
       (Ap (sgroup_map (monoid_sgroup_hom f0)) (group_inverse G y))
       (Ap (sgroup_map (monoid_sgroup_hom f0)) (group_inverse G x)));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G'
       (Ap (sgroup_map (monoid_sgroup_hom f0)) (group_inverse G x))
       (Ap (sgroup_map (monoid_sgroup_hom f0)) (group_inverse G y)));
 auto with algebra.
apply
 Trans
  with
    (Ap (sgroup_map (monoid_sgroup_hom f0)) (group_inverse G (monoid_unit G)));
 auto with algebra.
apply Trans with (Ap (sgroup_map (monoid_sgroup_hom f0)) (monoid_unit G));
 auto with algebra.
Defined.

Definition group_hom : ABELIAN_GROUP.
apply
 (BUILD_ABELIAN_GROUP (E:=Hom G G') (genlaw:=group_hom_law)
    (e:=group_hom_unit) (geninv:=group_hom_inv)).
intros x x' y y' H' H'0; try assumption.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros x y z; try assumption.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros x; try assumption.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros x y H'; try assumption.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros x; try assumption.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
intros x y; try assumption.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Defined.

Lemma group_hom_law_prop :
 forall (f g : group_hom) (x : G),
 Equal (sgroup_law _ f g x) (sgroup_law _ (f x) (g x)).
simpl in |- *; auto with algebra.
Qed.

Lemma group_hom_unit_prop :
 forall x : G, Equal (monoid_unit group_hom x) (monoid_unit G').
simpl in |- *; auto with algebra.
Qed.

Lemma group_hom_inv_prop :
 forall (f : group_hom) (x : G),
 Equal (group_inverse group_hom f x) (group_inverse G' (f x)).
simpl in |- *; auto with algebra.
Qed.
End Def.
Hint Resolve group_hom_law_prop group_hom_unit_prop group_hom_inv_prop:
  algebra.