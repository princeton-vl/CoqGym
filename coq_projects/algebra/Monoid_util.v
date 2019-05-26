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
Require Export Sub_monoid.
Require Export Abelian_group_cat.
(** Title "Tools for building monoids." *)
Section Monoid.
Variable E : Setoid.
Variable genlaw : E -> E -> E.
Variable e : E.
Hypothesis
  fcomp :
    forall x x' y y' : E,
    Equal x x' -> Equal y y' -> Equal (genlaw x y) (genlaw x' y').
Hypothesis
  genlawassoc :
    forall x y z : E, Equal (genlaw (genlaw x y) z) (genlaw x (genlaw y z)).
Hypothesis eunitgenlawr : forall x : E, Equal (genlaw x e) x.
Hypothesis eunitgenlawl : forall x : E, Equal (genlaw e x) x.

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

Definition sg := Build_sgroup (Build_sgroup_on fassoc).

Definition BUILD_MONOID : MONOID :=
  Build_monoid (Build_monoid_on (A:=sg) (monoid_unit:=e) eunitr eunitl).
End Monoid.
Section Abelian_monoid.
Variable E : Setoid.
Variable genlaw : E -> E -> E.
Variable e : E.
Hypothesis
  fcomp :
    forall x x' y y' : E,
    Equal x x' -> Equal y y' -> Equal (genlaw x y) (genlaw x' y').
Hypothesis
  genlawassoc :
    forall x y z : E, Equal (genlaw (genlaw x y) z) (genlaw x (genlaw y z)).
Hypothesis eunitgenlawr : forall x : E, Equal (genlaw x e) x.
Hypothesis eunitgenlawl : forall x : E, Equal (genlaw e x) x.
Hypothesis fcom : forall x y : E, Equal (genlaw x y) (genlaw y x).

Definition M := BUILD_MONOID fcomp genlawassoc eunitgenlawr eunitgenlawl.

Definition asg : abelian_sgroup.
apply (Build_abelian_sgroup (abelian_sgroup_sgroup:=M)).
apply (Build_abelian_sgroup_on (A:=M)).
abstract (red in |- *; simpl in |- *; exact fcom).
Defined.

Definition BUILD_ABELIAN_MONOID : ABELIAN_MONOID :=
  Build_abelian_monoid (Build_abelian_monoid_on (M:=M) asg).
End Abelian_monoid.
Section Hom.
Variable G G' : MONOID.
Variable ff : G -> G'.
Hypothesis ffcomp : forall x y : G, Equal x y -> Equal (ff x) (ff y).
Hypothesis
  fflaw :
    forall x y : G,
    Equal (ff (sgroup_law _ x y)) (sgroup_law _ (ff x) (ff y)).
Hypothesis ffunit : Equal (ff (monoid_unit G)) (monoid_unit G').

Definition f2 := Build_Map ffcomp.

Definition fhomsg := Build_sgroup_hom (sgroup_map:=f2) fflaw.

Definition BUILD_HOM_MONOID : Hom G G' :=
  Build_monoid_hom (monoid_sgroup_hom:=fhomsg) ffunit.
End Hom.
Section Build_sub_monoid.
Variable G : MONOID.
Variable H : part_set G.
Hypothesis
  Hlaw :
    forall x y : G,
    in_part x H -> in_part y H -> in_part (sgroup_law _ x y) H.
Hypothesis Hunit : in_part (monoid_unit G) H.

Definition BUILD_SUB_MONOID : submonoid G :=
  Build_submonoid (G:=G) (submonoid_subsgroup:=Build_subsgroup Hlaw) Hunit.
End Build_sub_monoid.
