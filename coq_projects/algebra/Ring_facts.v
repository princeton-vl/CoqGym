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
Require Export Ring_cat.
Require Export Group_facts.
Require Export Abelian_group_facts.
(** Title "Basic properties of rings." *)
Section Lemmas.
Variable R : RING.

Lemma RING_assoc :
 forall x y z : R,
 Equal (ring_mult (ring_mult x y) z) (ring_mult x (ring_mult y z)).
exact (sgroup_assoc_prf (E:=R) (ring_monoid R)).
Qed.

Lemma RING_comp :
 forall x x' y y' : R,
 Equal x x' -> Equal y y' -> Equal (ring_mult x y) (ring_mult x' y').
unfold ring_mult in |- *; auto with algebra.
Qed.

Lemma RING_unit_r : forall x : R, Equal (ring_mult x (ring_unit R)) x.
exact (monoid_unit_r_prf (ring_monoid R)).
Qed.

Lemma RING_unit_l : forall x : R, Equal (ring_mult (ring_unit R) x) x.
exact (monoid_unit_l_prf (ring_monoid R)).
Qed.

Lemma RING_dist_r :
 forall x y z : R,
 Equal (ring_mult (sgroup_law R x y) z)
   (sgroup_law R (ring_mult x z) (ring_mult y z)).
exact (ring_dist_r_prf R).
Qed.

Lemma RING_dist_l :
 forall x y z : R,
 Equal (ring_mult x (sgroup_law R y z))
   (sgroup_law R (ring_mult x y) (ring_mult x z)).
exact (ring_dist_l_prf R).
Qed.
Hint Resolve RING_assoc RING_comp RING_unit_r RING_unit_l RING_dist_r
  RING_dist_l: algebra.

Lemma RING_absorbant_r :
 forall x : R, Equal (ring_mult x (monoid_unit R)) (monoid_unit R).
intros x; try assumption.
apply GROUP_reg_right with (ring_mult x (monoid_unit R)).
apply Trans with (ring_mult x (sgroup_law R (monoid_unit R) (monoid_unit R)));
 auto with algebra.
apply Trans with (ring_mult x (monoid_unit R)); auto with algebra.
Qed.
Hint Resolve RING_absorbant_r: algebra.

Lemma RING_absorbant_l :
 forall x : R, Equal (ring_mult (monoid_unit R) x) (monoid_unit R).
intros x; try assumption.
apply GROUP_reg_right with (ring_mult (monoid_unit R) x).
apply Trans with (ring_mult (sgroup_law R (monoid_unit R) (monoid_unit R)) x);
 auto with algebra.
apply Trans with (ring_mult (monoid_unit R) x); auto with algebra.
Qed.
Hint Resolve RING_absorbant_l: algebra.

Lemma RING_op_mult_l :
 forall x y : R,
 Equal (ring_mult (group_inverse R x) y) (group_inverse R (ring_mult x y)).
intros x y; try assumption.
apply Sym.
apply GROUP_law_inverse.
apply Trans with (ring_mult (sgroup_law R x (group_inverse R x)) y);
 auto with algebra.
apply Trans with (ring_mult (monoid_unit R) y); auto with algebra.
Qed.
Hint Resolve RING_op_mult_l: algebra.

Lemma RING_op_mult_r :
 forall x y : R,
 Equal (ring_mult x (group_inverse R y)) (group_inverse R (ring_mult x y)).
intros x y; try assumption.
apply Sym.
apply GROUP_law_inverse.
apply Trans with (ring_mult x (sgroup_law R y (group_inverse R y)));
 auto with algebra.
apply Trans with (ring_mult x (monoid_unit R)); auto with algebra.
Qed.
End Lemmas.
Hint Resolve RING_assoc RING_comp RING_unit_r RING_unit_l RING_dist_r
  RING_dist_l RING_absorbant_r RING_absorbant_l RING_op_mult_l
  RING_op_mult_r: algebra.
Section Commutative_rings.
Variable R1 : CRING.

Lemma CRING_com : forall x y : R1, Equal (ring_mult x y) (ring_mult y x).
exact (cring_com_prf R1).
Qed.
Hint Immediate CRING_com: algebra.

Lemma CRING_mult4 :
 forall a b c d : R1,
 Equal (ring_mult (ring_mult a b) (ring_mult c d))
   (ring_mult (ring_mult a c) (ring_mult b d)).
intros a b c d; try assumption.
apply Trans with (ring_mult a (ring_mult b (ring_mult c d)));
 auto with algebra.
apply Trans with (ring_mult a (ring_mult (ring_mult b c) d));
 auto with algebra.
apply Trans with (ring_mult a (ring_mult (ring_mult c b) d));
 auto with algebra.
apply Trans with (ring_mult a (ring_mult c (ring_mult b d)));
 auto with algebra.
Qed.
Hint Resolve CRING_mult4: algebra.

Lemma CRING_mult3 :
 forall x y z : R1,
 Equal (ring_mult x (ring_mult y z)) (ring_mult y (ring_mult x z)).
intros x y z; try assumption.
apply Trans with (ring_mult (ring_mult x y) z); auto with algebra.
apply Trans with (ring_mult (ring_mult y x) z); auto with algebra.
Qed.
Hint Resolve CRING_mult3: algebra.

Lemma CRING_mult3bis :
 forall x y z : R1,
 Equal (ring_mult (ring_mult x y) z) (ring_mult (ring_mult x z) y).
intros x y z; try assumption.
apply Trans with (ring_mult z (ring_mult x y)); auto with algebra.
apply Trans with (ring_mult z (ring_mult y x)); auto with algebra.
apply Trans with (ring_mult y (ring_mult z x)); auto with algebra.
apply Trans with (ring_mult (ring_mult z x) y); auto with algebra.
Qed.
Hint Resolve CRING_mult3bis: algebra.
End Commutative_rings.
Hint Resolve CRING_mult4 CRING_mult3 CRING_mult3bis: algebra.
Hint Immediate CRING_com: algebra.
Section Hom_lemmas.
Hint Resolve RING_comp: algebra.
Variable R R' : RING.
Variable f : Hom R R'.

Lemma RING_hom_prop :
 forall x y : R, Equal (f (ring_mult x y)) (ring_mult (f x) (f y)).
case f; auto with algebra.
Qed.

Lemma RING_one_prop : Equal (f (ring_unit R)) (ring_unit R').
case f; auto with algebra.
Qed.

Lemma RING_hom_ext :
 forall f g : Hom R R', (forall x : R, Equal (f x) (g x)) -> Equal f g.
auto with algebra.
Qed.
End Hom_lemmas.
Hint Resolve RING_hom_prop RING_one_prop: algebra.