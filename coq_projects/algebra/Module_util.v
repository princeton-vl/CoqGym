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


Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Module_cat.
Require Export Monoid_util.
Require Export Group_util.
(** Title "Tools for building modules." *)
Section Module.
Variable R : RING.
Variable E : Setoid.
Variable genlaw : E -> E -> E.
Variable e : E.
Variable geninv : E -> E.
Variable gen_module_op : R -> E -> E.
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
Hypothesis
  op_comp :
    forall (a b : R) (x y : E),
    Equal a b -> Equal x y -> Equal (gen_module_op a x) (gen_module_op b y).
Hypothesis
  oplin_l :
    forall (a b : R) (x : E),
    Equal (gen_module_op (sgroup_law R a b) x)
      (genlaw (gen_module_op a x) (gen_module_op b x)).
Hypothesis
  oplin_r :
    forall (a : R) (x y : E),
    Equal (gen_module_op a (genlaw x y))
      (genlaw (gen_module_op a x) (gen_module_op a y)).
Hypothesis
  opassoc :
    forall (a b : R) (x : E),
    Equal (gen_module_op a (gen_module_op b x))
      (gen_module_op (ring_mult a b) x).
Hypothesis opunit : forall x : E, Equal (gen_module_op (ring_unit R) x) x.

Definition module_util_endo_el : forall a : R, Endo_SET E.
intros a; try assumption.
simpl in |- *.
apply (Build_Map (A:=E) (B:=E) (Ap:=fun x : E => gen_module_op a x)).
red in |- *.
auto with algebra.
Defined.

Definition module_util_op : operation (ring_monoid R) E.
simpl in |- *.
apply
 (BUILD_HOM_MONOID (G:=ring_monoid R) (G':=Endo_SET E)
    (ff:=module_util_endo_el)).
simpl in |- *.
intros x y H'; red in |- *.
simpl in |- *.
auto with algebra.
simpl in |- *.
intros x y; red in |- *.
simpl in |- *.
intros x0; try assumption.
apply Trans with (gen_module_op (ring_mult x y) x0); auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Defined.

Definition module_util_G : ABELIAN_GROUP.
apply (BUILD_ABELIAN_GROUP (E:=E) (genlaw:=genlaw) (e:=e) (geninv:=geninv));
 auto with algebra.
Defined.

Definition BUILD_MODULE : MODULE R.
apply (Build_module (R:=R) (module_carrier:=module_util_G)).
apply (Build_module_on (R:=R) (M:=module_util_G) (module_op:=module_util_op)).
abstract exact oplin_l.
abstract exact oplin_r.
Defined.
End Module.
Section Hom.
Variable R : RING.
Variable Mod Mod' : MODULE R.
Variable ff : Mod -> Mod'.
Hypothesis ffcomp : forall x y : Mod, Equal x y -> Equal (ff x) (ff y).
Hypothesis
  fflaw :
    forall x y : Mod,
    Equal (ff (sgroup_law Mod x y)) (sgroup_law Mod' (ff x) (ff y)).
Hypothesis ffunit : Equal (ff (monoid_unit Mod)) (monoid_unit Mod').
Hypothesis
  ffop :
    forall (a : R) (x : Mod),
    Equal (ff (module_mult a x)) (module_mult a (ff x)).

Definition BUILD_HOM_MODULE : Hom Mod Mod' :=
  Build_module_hom
    (module_monoid_hom:=BUILD_HOM_GROUP (G:=Mod) (G':=Mod') (ff:=ff) ffcomp
                          fflaw ffunit) ffop.
End Hom.
Section Module_on_group.
Variable R : RING.
Variable module_util_G : ABELIAN_GROUP.
Variable gen_module_op : R -> module_util_G -> module_util_G.
Hypothesis
  op_comp :
    forall (a b : R) (x y : module_util_G),
    Equal a b -> Equal x y -> Equal (gen_module_op a x) (gen_module_op b y).
Hypothesis
  oplin_l :
    forall (a b : R) (x : module_util_G),
    Equal (gen_module_op (sgroup_law R a b) x)
      (sgroup_law module_util_G (gen_module_op a x) (gen_module_op b x)).
Hypothesis
  oplin_r :
    forall (a : R) (x y : module_util_G),
    Equal (gen_module_op a (sgroup_law module_util_G x y))
      (sgroup_law module_util_G (gen_module_op a x) (gen_module_op a y)).
Hypothesis
  opassoc :
    forall (a b : R) (x : module_util_G),
    Equal (gen_module_op a (gen_module_op b x))
      (gen_module_op (ring_mult a b) x).
Hypothesis
  opunit : forall x : module_util_G, Equal (gen_module_op (ring_unit R) x) x.

Definition module_util_endo_el2 : forall a : R, Endo_SET module_util_G.
intros a; try assumption.
simpl in |- *.
apply
 (Build_Map (A:=module_util_G) (B:=module_util_G)
    (Ap:=fun x : module_util_G => gen_module_op a x)).
red in |- *.
auto with algebra.
Defined.

Definition module_util_op2 : operation (ring_monoid R) module_util_G.
simpl in |- *.
apply
 (BUILD_HOM_MONOID (G:=ring_monoid R) (G':=Endo_SET module_util_G)
    (ff:=module_util_endo_el2)).
simpl in |- *.
intros x y H'; red in |- *.
simpl in |- *.
auto with algebra.
simpl in |- *.
intros x y; red in |- *.
simpl in |- *.
intros x0; try assumption.
apply Trans with (gen_module_op (ring_mult x y) x0); auto with algebra.
simpl in |- *.
red in |- *.
simpl in |- *.
auto with algebra.
Defined.

Definition BUILD_MODULE_GROUP : MODULE R.
apply (Build_module (R:=R) (module_carrier:=module_util_G)).
apply
 (Build_module_on (R:=R) (M:=module_util_G) (module_op:=module_util_op2)).
abstract exact oplin_l.
abstract exact oplin_r.
Defined.
End Module_on_group.