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
Require Export Module_util.
Require Export Ring_facts.
Require Export Module_facts.
Section Hom_module_def.
Variable R : CRING.
Variable Mod1 Mod2 : MODULE R.

Definition add_hom_module : forall f g : Hom Mod1 Mod2, Hom Mod1 Mod2.
intros f0 g.
apply
 (BUILD_HOM_MODULE (R:=R) (Mod:=Mod1) (Mod':=Mod2)
    (ff:=fun x : Mod1 => sgroup_law Mod2 (f0 x) (g x))).
abstract auto with algebra.
abstract (intros x y;
           apply
            Trans
             with
               (sgroup_law (module_carrier Mod2)
                  (sgroup_law (module_carrier Mod2)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) y))
                  (sgroup_law (module_carrier Mod2)
                     (Ap
                        (sgroup_map (monoid_sgroup_hom (module_monoid_hom g)))
                        x)
                     (Ap
                        (sgroup_map (monoid_sgroup_hom (module_monoid_hom g)))
                        y))); auto with algebra).
abstract (apply
           Trans
            with
              (sgroup_law (module_carrier Mod2)
                 (monoid_unit (module_carrier Mod2))
                 (monoid_unit (module_carrier Mod2))); 
           auto with algebra).
abstract (intros a x;
           apply
            Trans
             with
               (sgroup_law (module_carrier Mod2)
                  (module_mult a
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x))
                  (module_mult a
                     (Ap
                        (sgroup_map (monoid_sgroup_hom (module_monoid_hom g)))
                        x))); auto with algebra).
Defined.

Definition zero_hom_module : Hom Mod1 Mod2.
apply
 (BUILD_HOM_MODULE (R:=R) (Mod:=Mod1) (Mod':=Mod2)
    (ff:=fun x : Mod1 => monoid_unit Mod2)); abstract 
 auto with algebra.
Defined.

Definition opp_hom_module : forall f : Hom Mod1 Mod2, Hom Mod1 Mod2.
intros f0.
apply
 (BUILD_HOM_MODULE (R:=R) (Mod:=Mod1) (Mod':=Mod2)
    (ff:=fun x : Mod1 => group_inverse Mod2 (f0 x))).
abstract auto with algebra.
abstract (intros x y;
           apply
            Trans
             with
               (group_inverse (module_carrier Mod2)
                  (sgroup_law (module_carrier Mod2)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) y)));
           auto with algebra;
           apply
            Trans
             with
               (group_inverse (module_carrier Mod2)
                  (sgroup_law (module_carrier Mod2)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) y)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x)));
           auto with algebra).
abstract (apply
           Trans
            with
              (group_inverse (module_carrier Mod2)
                 (monoid_unit (module_carrier Mod2))); 
           auto with algebra).
abstract (intros a x;
           apply
            Trans
             with
               (group_inverse (module_carrier Mod2)
                  (module_mult a
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x)));
           auto with algebra).
Defined.

Definition mult_hom_module :
  forall (a : R) (f : Hom Mod1 Mod2), Hom Mod1 Mod2.
intros a f0.
apply
 (BUILD_HOM_MODULE (R:=R) (Mod:=Mod1) (Mod':=Mod2)
    (ff:=fun x : Mod1 => module_mult a (f0 x))).
abstract auto with algebra.
abstract (intros x y;
           apply
            Trans
             with
               (module_mult a
                  (sgroup_law (module_carrier Mod2)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x)
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) y)));
           auto with algebra).
abstract (apply
           Trans with (module_mult a (monoid_unit (module_carrier Mod2)));
           auto with algebra).
abstract (intros a0 x;
           apply
            Trans
             with
               (module_mult a
                  (module_mult a0
                     (Ap
                        (sgroup_map
                           (monoid_sgroup_hom (module_monoid_hom f0))) x)));
           auto with algebra;
           apply
            Trans
             with
               (module_mult (ring_mult a a0)
                  (Ap (sgroup_map (monoid_sgroup_hom (module_monoid_hom f0)))
                     x)); auto with algebra;
           apply
            Trans
             with
               (module_mult (ring_mult a0 a)
                  (Ap (sgroup_map (monoid_sgroup_hom (module_monoid_hom f0)))
                     x)); auto with algebra).
Defined.

Definition Hom_module : MODULE R.
apply
 (BUILD_MODULE (R:=R) (E:=Hom Mod1 Mod2) (genlaw:=add_hom_module)
    (e:=zero_hom_module) (geninv:=opp_hom_module)
    (gen_module_op:=mult_hom_module));
 try
  abstract (simpl in |- *; unfold Map_eq in |- *; simpl in |- *;
             auto with algebra).
Defined.
End Hom_module_def.
