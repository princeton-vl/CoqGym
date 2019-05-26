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
Require Export Sub_group.
Require Export Abelian_group_cat.
(** Title "Tools for building groups." *)
Section Group.
Variable E : Setoid.
Variable genlaw : E -> E -> E.
Variable e : E.
Variable geninv : E -> E.
Hypothesis
  fcomp :
    forall x x' y y' : E,
    Equal x x' -> Equal y y' -> Equal (genlaw x y) (genlaw x' y').
Hypothesis
  genlawassoc :
    forall x y z : E, Equal (genlaw (genlaw x y) z) (genlaw x (genlaw y z)).
Hypothesis eunitgenlawr : forall x : E, Equal (genlaw x e) x.
Hypothesis invcomp : forall x y : E, Equal x y -> Equal (geninv x) (geninv y).
Hypothesis geninvr : forall x : E, Equal (genlaw x (geninv x)) e.

Lemma geninvl : forall x : E, Equal (genlaw (geninv x) x) e.
intros x; try assumption.
apply Trans with (genlaw (genlaw (geninv x) x) e); auto with algebra.
apply
 Trans
  with (genlaw (genlaw (geninv x) x) (genlaw (geninv x) (geninv (geninv x))));
 auto with algebra.
apply
 Trans
  with (genlaw (geninv x) (genlaw x (genlaw (geninv x) (geninv (geninv x)))));
 auto with algebra.
apply
 Trans
  with (genlaw (geninv x) (genlaw (genlaw x (geninv x)) (geninv (geninv x))));
 auto with algebra.
apply Trans with (genlaw (geninv x) (genlaw e (geninv (geninv x))));
 auto with algebra.
apply Trans with (genlaw (genlaw (geninv x) e) (geninv (geninv x)));
 auto with algebra.
apply Trans with (genlaw (geninv x) (geninv (geninv x))); auto with algebra.
Qed.
Hint Resolve geninvl: algebra.

Lemma eunitgenlawl : forall x : E, Equal (genlaw e x) x.
intros x; try assumption.
apply Trans with (genlaw (genlaw x (geninv x)) x); auto with algebra.
apply Trans with (genlaw x (genlaw (geninv x) x)); auto with algebra.
apply Trans with (genlaw x e); auto with algebra.
Qed.
Hint Resolve eunitgenlawl: algebra.

Definition f := uncurry fcomp.

Lemma fassoc : associative f.
red in |- *.
simpl in |- *; auto with algebra.
Qed.

Lemma eunitr : unit_r f e.
red in |- *.
simpl in |- *; auto with algebra.
Qed.

Lemma eunitl : unit_l f e.
red in |- *.
simpl in |- *; auto with algebra.
Qed.

Definition inv := Build_Map (Ap:=geninv) invcomp.

Lemma invr : inverse_r f e inv.
red in |- *.
simpl in |- *; auto with algebra.
Qed.

Lemma invl : inverse_l f e inv.
red in |- *.
simpl in |- *; auto with algebra.
Qed.

Definition sg := Build_sgroup (Build_sgroup_on fassoc).

Definition m :=
  Build_monoid (Build_monoid_on (A:=sg) (monoid_unit:=e) eunitr eunitl).

Definition BUILD_GROUP : GROUP :=
  Build_group (Build_group_on (G:=m) (group_inverse_map:=inv) invr invl).
End Group.
Section Abelian_group.
Variable E : Setoid.
Variable genlaw : E -> E -> E.
Variable e : E.
Variable geninv : E -> E.
Hypothesis
  fcomp :
    forall x x' y y' : E,
    Equal x x' -> Equal y y' -> Equal (genlaw x y) (genlaw x' y').
Hypothesis
  genlawassoc :
    forall x y z : E, Equal (genlaw (genlaw x y) z) (genlaw x (genlaw y z)).
Hypothesis eunitgenlawr : forall x : E, Equal (genlaw x e) x.
Hypothesis invcomp : forall x y : E, Equal x y -> Equal (geninv x) (geninv y).
Hypothesis geninvr : forall x : E, Equal (genlaw x (geninv x)) e.
Hypothesis fcom : forall x y : E, Equal (genlaw x y) (genlaw y x).

Definition G := BUILD_GROUP fcomp genlawassoc eunitgenlawr invcomp geninvr.

Definition asg : abelian_sgroup.
apply (Build_abelian_sgroup (abelian_sgroup_sgroup:=G)).
apply (Build_abelian_sgroup_on (A:=G)).
abstract (red in |- *; simpl in |- *; auto with algebra).
Defined.

Definition BUILD_ABELIAN_GROUP : ABELIAN_GROUP :=
  Build_abelian_group
    (Build_abelian_group_on (G:=G)
       (Build_abelian_monoid (Build_abelian_monoid_on (M:=G) asg))).
End Abelian_group.
Section Hom.
Variable G G' : GROUP.
Variable ff : G -> G'.
Hypothesis ffcomp : forall x y : G, Equal x y -> Equal (ff x) (ff y).
Hypothesis
  fflaw :
    forall x y : G,
    Equal (ff (sgroup_law _ x y)) (sgroup_law _ (ff x) (ff y)).
Hypothesis ffunit : Equal (ff (monoid_unit G)) (monoid_unit G').

Definition f2 := Build_Map ffcomp.

Definition fhomsg := Build_sgroup_hom (sgroup_map:=f2) fflaw.

Definition BUILD_HOM_GROUP : Hom G G' :=
  Build_monoid_hom (monoid_sgroup_hom:=fhomsg) ffunit.
End Hom.
Section Build_sub_group.
Variable G : GROUP.
Variable H : part_set G.
Hypothesis
  Hlaw :
    forall x y : G,
    in_part x H -> in_part y H -> in_part (sgroup_law _ x y) H.
Hypothesis Hunit : in_part (monoid_unit G) H.
Hypothesis Hinv : forall x : G, in_part x H -> in_part (group_inverse _ x) H.

Definition BUILD_SUB_GROUP : subgroup G :=
  Build_subgroup (G:=G)
    (subgroup_submonoid:=Build_submonoid (G:=G)
                           (submonoid_subsgroup:=Build_subsgroup Hlaw) Hunit)
    Hinv.
End Build_sub_group.