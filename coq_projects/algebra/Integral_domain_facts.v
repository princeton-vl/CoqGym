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
Require Export Integral_domain_cat.
Require Export Ring_facts.
Require Export Classical_Prop.
(** Title "Basic properties of  integral domains." *)
Section Lemmas.
Variable R : INTEGRAL_DOMAIN.

Lemma INTEGRAL_DOMAIN_prop_rev :
 forall x y : R,
 ~ Equal x (monoid_unit R) ->
 ~ Equal y (monoid_unit R) -> ~ Equal (ring_mult x y) (monoid_unit R).
exact (idomain_prf R).
Qed.

Lemma INTEGRAL_DOMAIN_prop :
 forall x y : R,
 Equal (ring_mult x y) (monoid_unit R) ->
 Equal x (monoid_unit R) \/ Equal y (monoid_unit R).
intros x y H'; try assumption.
generalize (INTEGRAL_DOMAIN_prop_rev (x:=x) (y:=y)).
apply NNPP; tauto.
Qed.

Lemma INTEGRAL_DOMAIN_mult_l :
 forall x y : R,
 ~ Equal (ring_mult x y) (monoid_unit R) -> ~ Equal x (monoid_unit R).
unfold not in |- *.
intros x y H' H'0; try assumption.
absurd (Equal (ring_mult x y) (monoid_unit R)); auto with algebra.
apply Trans with (ring_mult (monoid_unit R) y); auto with algebra.
Qed.

Lemma INTEGRAL_DOMAIN_mult_r :
 forall x y : R,
 ~ Equal (ring_mult x y) (monoid_unit R) -> ~ Equal y (monoid_unit R).
unfold not in |- *.
intros x y H' H'0; try assumption.
absurd (Equal (ring_mult x y) (monoid_unit R)); auto with algebra.
apply Trans with (ring_mult x (monoid_unit R)); auto with algebra.
Qed.

Lemma INTEGRAL_DOMAIN_mult_n0_r :
 forall x y : R,
 Equal (ring_mult x y) (monoid_unit R) ->
 ~ Equal y (monoid_unit R) -> Equal x (monoid_unit R).
intros x y H' H'0; try assumption.
intuition.
elim (INTEGRAL_DOMAIN_prop (x:=x) (y:=y)); auto with algebra.
intros H'1; try assumption.
absurd (Equal y (monoid_unit R)); auto with algebra.
Qed.

Lemma INTEGRAL_DOMAIN_mult_n0_l :
 forall x y : R,
 Equal (ring_mult x y) (monoid_unit R) ->
 ~ Equal x (monoid_unit R) -> Equal y (monoid_unit R).
intros x y H' H'0; try assumption.
elim (INTEGRAL_DOMAIN_prop (x:=x) (y:=y)); auto with algebra.
intros H'1; try assumption.
absurd (Equal x (monoid_unit R)); auto with algebra.
Qed.
Hint Resolve INTEGRAL_DOMAIN_prop INTEGRAL_DOMAIN_prop_rev
  INTEGRAL_DOMAIN_mult_l INTEGRAL_DOMAIN_mult_r INTEGRAL_DOMAIN_mult_n0_l
  INTEGRAL_DOMAIN_mult_n0_r: algebra.

Lemma INTEGRAL_DOMAIN_simpl_r :
 forall x y z : R,
 ~ Equal z (monoid_unit R) ->
 Equal (ring_mult x z) (ring_mult y z) -> Equal x y.
intros x y z H' H'0; try assumption.
cut
 (Equal (ring_mult (sgroup_law R x (group_inverse R y)) z) (monoid_unit R)).
intros H'1; try assumption.
cut (Equal (sgroup_law R x (group_inverse R y)) (monoid_unit R)).
intros H'2; try assumption.
apply GROUP_reg_right with (group_inverse R y); auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply INTEGRAL_DOMAIN_mult_n0_r with z; auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult x z) (ring_mult (group_inverse R y) z));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult x z) (group_inverse R (ring_mult y z)));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult x z) (group_inverse R (ring_mult x z)));
 auto with algebra.
Qed.

Lemma INTEGRAL_DOMAIN_simpl_l :
 forall x y z : R,
 ~ Equal z (monoid_unit R) ->
 Equal (ring_mult z x) (ring_mult z y) -> Equal x y.
intros x y z H' H'0; try assumption.
cut
 (Equal (ring_mult z (sgroup_law R x (group_inverse R y))) (monoid_unit R)).
intros H'1; try assumption.
cut (Equal (sgroup_law R x (group_inverse R y)) (monoid_unit R)).
intros H'2; try assumption.
apply GROUP_reg_right with (group_inverse R y); auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply INTEGRAL_DOMAIN_mult_n0_l with z; auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult z x) (ring_mult z (group_inverse R y)));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult z x) (group_inverse R (ring_mult z y)));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult z x) (group_inverse R (ring_mult z x)));
 auto with algebra.
Qed.

Lemma INTEGRAL_DOMAIN_mult_eq_r :
 forall x y z : R,
 Equal (ring_mult x z) (ring_mult y z) ->
 Equal x y \/ Equal z (monoid_unit R).
intros x y z H'; try assumption.
cut
 (Equal (ring_mult (sgroup_law R x (group_inverse R y)) z) (monoid_unit R)).
intros H'0; try assumption.
elim (INTEGRAL_DOMAIN_prop (x:=sgroup_law R x (group_inverse R y)) (y:=z));
 auto with algebra.
intros H'1; try assumption.
left; try assumption.
apply GROUP_reg_right with (group_inverse R y); auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult x z) (ring_mult (group_inverse R y) z));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult x z) (group_inverse R (ring_mult y z)));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult x z) (group_inverse R (ring_mult x z)));
 auto with algebra.
Qed.

Lemma INTEGRAL_DOMAIN_mult_eq_l :
 forall x y z : R,
 Equal (ring_mult z x) (ring_mult z y) ->
 Equal x y \/ Equal z (monoid_unit R).
intros x y z H'; try assumption.
cut
 (Equal (ring_mult z (sgroup_law R x (group_inverse R y))) (monoid_unit R)).
intros H'0; try assumption.
elim (INTEGRAL_DOMAIN_prop (x:=z) (y:=sgroup_law R x (group_inverse R y)));
 auto with algebra.
intros H'1; try assumption.
left; try assumption.
apply GROUP_reg_right with (group_inverse R y); auto with algebra.
apply Trans with (monoid_unit R); auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult z x) (ring_mult z (group_inverse R y)));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult z x) (group_inverse R (ring_mult z y)));
 auto with algebra.
apply
 Trans with (sgroup_law R (ring_mult z x) (group_inverse R (ring_mult z x)));
 auto with algebra.
Qed.
End Lemmas.
Hint Resolve INTEGRAL_DOMAIN_prop INTEGRAL_DOMAIN_prop_rev
  INTEGRAL_DOMAIN_mult_l INTEGRAL_DOMAIN_mult_r INTEGRAL_DOMAIN_mult_n0_l
  INTEGRAL_DOMAIN_mult_n0_r: algebra.
Hint Resolve INTEGRAL_DOMAIN_simpl_r INTEGRAL_DOMAIN_simpl_l: algebra.
