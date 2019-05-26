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
Require Export Group_cat.
Require Export Sgroup_facts.
Require Export Monoid_facts.
Section Lemmas.
Variable G : GROUP.

Lemma GROUP_comp :
 forall x x' : G,
 Equal x x' -> Equal (group_inverse _ x) (group_inverse _ x').
unfold group_inverse in |- *.
auto with algebra.
Qed.

Lemma GROUP_inverse_r :
 forall x : G, Equal (sgroup_law _ x (group_inverse _ x)) (monoid_unit G).
intros; apply (group_inverse_r_prf G x); auto with algebra.
Qed.

Lemma GROUP_inverse_l :
 forall x : G, Equal (sgroup_law _ (group_inverse _ x) x) (monoid_unit G).
intros; apply (group_inverse_l_prf G x); auto with algebra.
Qed.
Hint Resolve GROUP_comp GROUP_inverse_r GROUP_inverse_l: algebra.

Lemma GROUP_unit_inverse :
 Equal (group_inverse _ (monoid_unit G)) (monoid_unit G).
apply
 Trans with (sgroup_law _ (group_inverse _ (monoid_unit G)) (monoid_unit G));
 auto with algebra.
Qed.

Lemma GROUP_reg_left :
 forall x y z : G, Equal (sgroup_law _ x y) (sgroup_law _ x z) -> Equal y z.
intros x y z H'; try assumption.
apply Trans with (sgroup_law _ (sgroup_law _ (group_inverse _ x) x) y);
 auto with algebra.
apply Trans with (sgroup_law _ (monoid_unit G) y); auto with algebra.
apply Trans with (sgroup_law _ (group_inverse _ x) (sgroup_law _ x y));
 auto with algebra.
apply Trans with (sgroup_law _ (group_inverse _ x) (sgroup_law _ x z));
 auto with algebra.
apply Trans with (sgroup_law _ (sgroup_law _ (group_inverse _ x) x) z);
 auto with algebra.
apply Trans with (sgroup_law _ (monoid_unit G) z); auto with algebra.
Qed.

Lemma GROUP_reg_right :
 forall x y z : G, Equal (sgroup_law _ y x) (sgroup_law _ z x) -> Equal y z.
intros x y z H'; try assumption.
apply Trans with (sgroup_law _ y (sgroup_law _ x (group_inverse _ x)));
 auto with algebra.
apply Trans with (sgroup_law _ y (monoid_unit G)); auto with algebra.
apply Trans with (sgroup_law _ (sgroup_law _ y x) (group_inverse _ x));
 auto with algebra.
apply Trans with (sgroup_law _ (sgroup_law _ z x) (group_inverse _ x));
 auto with algebra.
apply Trans with (sgroup_law _ z (sgroup_law _ x (group_inverse _ x)));
 auto with algebra.
apply Trans with (sgroup_law _ z (monoid_unit G)); auto with algebra.
Qed.

Lemma GROUP_inverse_inverse :
 forall x : G, Equal (group_inverse _ (group_inverse _ x)) x.
intros x; try assumption.
apply GROUP_reg_right with (group_inverse _ x).
apply Trans with (monoid_unit G); auto with algebra.
Qed.

Lemma GROUP_law_inverse :
 forall x y : G,
 Equal (sgroup_law _ x y) (monoid_unit G) -> Equal (group_inverse _ x) y.
intros x y H'; try assumption.
apply GROUP_reg_left with x.
apply Trans with (monoid_unit G); auto with algebra.
Qed.

Lemma GROUP_inverse_law :
 forall x y : G,
 Equal (group_inverse _ (sgroup_law _ x y))
   (sgroup_law _ (group_inverse _ y) (group_inverse _ x)).
intros x y; try assumption.
apply GROUP_law_inverse.
apply
 Trans
  with
    (sgroup_law G x
       (sgroup_law G y (sgroup_law G (group_inverse _ y) (group_inverse _ x))));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G x
       (sgroup_law G (sgroup_law G y (group_inverse _ y)) (group_inverse _ x)));
 auto with algebra.
apply
 Trans
  with (sgroup_law G x (sgroup_law G (monoid_unit G) (group_inverse _ x)));
 auto with algebra.
apply Trans with (sgroup_law G x (group_inverse _ x)); auto with algebra.
Qed.
End Lemmas.
Section Lemmas2.
Variable G F : GROUP.
Variable f : Hom G F.

Lemma GROUP_hom_prop :
 forall x : G, Equal (f (group_inverse _ x)) (group_inverse _ (f x)).
intros x; try assumption.
apply Sym.
apply GROUP_law_inverse.
apply Trans with (f (sgroup_law _ x (group_inverse _ x))); auto with algebra.
apply Trans with (f (monoid_unit G)); auto with algebra.
cut (Equal (sgroup_law G x (group_inverse _ x)) (monoid_unit G)).
auto with algebra.
apply GROUP_inverse_r.
Qed.
End Lemmas2.
Hint Resolve GROUP_comp GROUP_inverse_r GROUP_inverse_l GROUP_unit_inverse
  GROUP_reg_left GROUP_reg_right GROUP_inverse_inverse GROUP_law_inverse
  GROUP_inverse_law: algebra.
Hint Resolve GROUP_hom_prop: algebra.
