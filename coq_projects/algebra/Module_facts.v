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
Require Export Abelian_group_facts.
Section Lemmas.
Variable R : RING.
Variable Mod : MODULE R.

Lemma MODULE_comp :
 forall (a b : R) (x y : Mod),
 Equal a b -> Equal x y -> Equal (module_mult a x) (module_mult b y).
intros a b x y H' H'0; try assumption.
apply Trans with (module_mult a y); unfold module_mult in |- *.
apply Ap_comp; auto with algebra.
apply Ap_comp; auto with algebra.
Qed.

Lemma MODULE_assoc :
 forall (a b : R) (x : Mod),
 Equal (module_mult (ring_mult a b) x) (module_mult a (module_mult b x)).
exact (operation_assoc (module_op Mod)).
Qed.

Lemma MODULE_dist_r :
 forall (a b : R) (x : Mod),
 Equal (module_mult (sgroup_law R a b) x)
   (sgroup_law Mod (module_mult a x) (module_mult b x)).
exact (module_op_lin_left_prf Mod).
Qed.

Lemma MODULE_dist_l :
 forall (a : R) (x y : Mod),
 Equal (module_mult a (sgroup_law Mod x y))
   (sgroup_law Mod (module_mult a x) (module_mult a y)).
exact (module_op_lin_right_prf Mod).
Qed.

Lemma MODULE_unit_l : forall x : Mod, Equal (module_mult (ring_unit R) x) x.
exact (operation_unit (module_op Mod)).
Qed.
Hint Resolve MODULE_comp MODULE_dist_r MODULE_dist_l MODULE_assoc
  MODULE_unit_l: algebra.

Lemma MODULE_absorbant_l :
 forall x : Mod, Equal (module_mult (monoid_unit R) x) (monoid_unit Mod).
intros x; try assumption.
apply GROUP_reg_left with (module_mult (monoid_unit R) x); auto with algebra.
apply
 Trans with (module_mult (sgroup_law R (monoid_unit R) (monoid_unit R)) x);
 auto with algebra.
apply Trans with (module_mult (monoid_unit R) x); auto with algebra.
Qed.

Lemma MODULE_absorbant_r :
 forall a : R, Equal (module_mult a (monoid_unit Mod)) (monoid_unit Mod).
intros a; try assumption.
apply GROUP_reg_left with (module_mult a (monoid_unit (module_carrier Mod)));
 auto with algebra.
apply
 Trans
  with (module_mult a (sgroup_law Mod (monoid_unit Mod) (monoid_unit Mod)));
 auto with algebra.
apply Trans with (module_mult a (monoid_unit Mod)); auto with algebra.
Qed.

Lemma MODULE_mult_op_r :
 forall (a : R) (x : Mod),
 Equal (module_mult a (group_inverse Mod x))
   (group_inverse Mod (module_mult a x)).
intros a x; try assumption.
apply Sym.
apply GROUP_law_inverse.
apply Trans with (module_mult a (sgroup_law Mod x (group_inverse Mod x)));
 auto with algebra.
apply Trans with (module_mult a (monoid_unit Mod)); auto with algebra.
apply MODULE_absorbant_r.
Qed.

Lemma MODULE_mult_op_l :
 forall (a : R) (x : Mod),
 Equal (module_mult (group_inverse R a) x)
   (group_inverse Mod (module_mult a x)).
intros a x; try assumption.
apply Sym.
apply GROUP_law_inverse.
apply Trans with (module_mult (sgroup_law R a (group_inverse R a)) x);
 auto with algebra.
apply Trans with (module_mult (monoid_unit R) x); auto with algebra.
apply MODULE_absorbant_l.
Qed.
Variable Mod' : MODULE R.
Variable f : Hom Mod Mod'.

Lemma MODULE_hom_prop :
 forall (a : R) (x : Mod), Equal (f (module_mult a x)) (module_mult a (f x)).
case f; auto with algebra.
Qed.
End Lemmas.
Hint Resolve MODULE_comp MODULE_assoc MODULE_dist_r MODULE_dist_l
  MODULE_unit_l MODULE_absorbant_l MODULE_absorbant_r MODULE_mult_op_l
  MODULE_mult_op_r MODULE_hom_prop: algebra.
