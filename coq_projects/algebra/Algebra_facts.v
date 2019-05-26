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
Require Export Algebra.
Require Export Ring_util.
Section Lemmas.
Variable R : CRING.
Variable A : algebra R.

Lemma ALGEBRA_comp :
 forall x x' y y' : A,
 Equal x x' -> Equal y y' -> Equal (algebra_mult x y) (algebra_mult x' y').
intros x x' y y' H' H'0; try assumption.
unfold algebra_mult in |- *.
apply Ap_comp.
auto with algebra.
apply
 (Ap_comp (B:=Hom_module (algebra_carrier A) (algebra_carrier A))
    (f:=algebra_bilinear_map (algebra_on_def A))
    (g:=algebra_bilinear_map (algebra_on_def A)) H').
auto with algebra.
Qed.

Lemma ALGEBRA_lin_right :
 forall x y z : A,
 Equal (algebra_mult x (sgroup_law A y z))
   (sgroup_law A (algebra_mult x y) (algebra_mult x z)).
intros x y z; try assumption.
unfold algebra_mult in |- *.
auto with algebra.
Qed.
Parameter
  ALGEBRA_lin_left :
    forall x y z : A,
    Equal (algebra_mult (sgroup_law A x y) z)
      (sgroup_law A (algebra_mult x z) (algebra_mult y z)).

Lemma ALGEBRA_mult_lin_right :
 forall (x y : A) (a : R),
 Equal (algebra_mult x (module_mult a y)) (module_mult a (algebra_mult x y)).
intros x y a; try assumption.
unfold algebra_mult in |- *.
auto with algebra.
Qed.
Parameter
  ALGEBRA_mult_lin_left :
    forall (x y : A) (a : R),
    Equal (algebra_mult (module_mult a x) y)
      (module_mult a (algebra_mult x y)).
End Lemmas.
Hint Resolve ALGEBRA_comp ALGEBRA_lin_right ALGEBRA_lin_left
  ALGEBRA_mult_lin_right ALGEBRA_mult_lin_left: algebra.
Section Lemmas2.
Variable R : CRING.
Variable A : ring_algebra R.

Lemma RING_ALGEBRA_assoc :
 forall x y z : A,
 Equal (algebra_mult (algebra_mult x y) z)
   (algebra_mult x (algebra_mult y z)).
exact (ring_algebra_assoc A).
Qed.

Lemma RING_ALGEBRA_unit_l :
 forall x : A, Equal (algebra_mult (ring_algebra_unit A) x) x.
exact (ring_algebra_unit_l A).
Qed.

Lemma RING_ALGEBRA_unit_r :
 forall x : A, Equal (algebra_mult x (ring_algebra_unit A)) x.
exact (ring_algebra_unit_r A).
Qed.
End Lemmas2.
Hint Resolve RING_ALGEBRA_assoc RING_ALGEBRA_unit_l RING_ALGEBRA_unit_r:
  algebra.
Section Ring_algebra_as_ring.
Variable R : CRING.
Variable A : ring_algebra R.

Definition ring_algebra_ring : ring.
apply
 (BUILD_RING (E:=A) (ringplus:=sgroup_law A)
    (ringmult:=algebra_mult (R:=R) (A:=A)) (zero:=monoid_unit A)
    (un:=ring_algebra_unit A) (ringopp:=group_inverse A)).
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
auto with algebra.
Defined.
End Ring_algebra_as_ring.
Coercion ring_algebra_ring : ring_algebra >-> ring.