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
Require Export Group_util.
(** Title "Quotient of a group by a normal sub-group." *)
Section Def.
Variable G : GROUP.
Variable H : subgroup G.

Definition normal :=
  forall x y : G,
  in_part y H ->
  in_part (sgroup_law _ x (sgroup_law _ y (group_inverse _ x))) H.
Hypothesis Hnormal : normal.

Definition group_quo_eq (x y : G) :=
  in_part (sgroup_law _ x (group_inverse _ y)) H.

Definition group_quo_eqrel : Relation G.
apply (Build_Relation (E:=G) (Rel_fun:=group_quo_eq)).
red in |- *.
unfold app_rel, group_quo_eq in |- *.
intros x x' y y' H' H'0 H'1; try assumption.
apply in_part_comp_l with (sgroup_law G x (group_inverse G y));
 auto with algebra.
Defined.

Lemma group_quo_eqrel_equiv : equivalence group_quo_eqrel.
red in Hnormal.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
intros x; red in |- *.
simpl in |- *.
unfold app_rel, group_quo_eq in |- *.
apply
 in_part_comp_l
  with (sgroup_law G x (sgroup_law G (monoid_unit G) (group_inverse G x)));
 auto with algebra.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
simpl in |- *.
unfold app_rel, group_quo_eq in |- *.
intros x y z H' H'0; try assumption.
apply
 in_part_comp_l
  with
    (sgroup_law G (sgroup_law G x (group_inverse G y))
       (sgroup_law G y (group_inverse G z))); auto with algebra.
apply
 Trans
  with
    (sgroup_law G x
       (sgroup_law G (group_inverse G y) (sgroup_law G y (group_inverse G z))));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G x
       (sgroup_law G (sgroup_law G (group_inverse G y) y) (group_inverse G z)));
 auto with algebra.
apply
 Trans
  with (sgroup_law G x (sgroup_law G (monoid_unit G) (group_inverse G z)));
 auto with algebra.
red in |- *.
simpl in |- *.
unfold app_rel, group_quo_eq in |- *.
intros x y H'; try assumption.
apply
 in_part_comp_l with (group_inverse G (sgroup_law G x (group_inverse G y)));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G (group_inverse G (group_inverse G y)) (group_inverse G x));
 auto with algebra.
Qed.

Definition group_quo_set := quotient G group_quo_eqrel group_quo_eqrel_equiv.

Lemma normal_com_in :
 forall x y : G, in_part (sgroup_law _ x y) H -> in_part (sgroup_law _ y x) H.
intros x y H'; try assumption.
apply
 in_part_comp_l
  with (sgroup_law G y (sgroup_law G (sgroup_law G x y) (group_inverse G y)));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply Trans with (sgroup_law G x (sgroup_law G y (group_inverse G y)));
 auto with algebra.
apply Trans with (sgroup_law G x (monoid_unit G)); auto with algebra.
Qed.
Hint Immediate normal_com_in: algebra.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_quo : group.
apply
 (BUILD_GROUP (E:=group_quo_set) (genlaw:=fun x y : G => sgroup_law _ x y)
    (e:=monoid_unit G) (geninv:=fun x : G => group_inverse _ x)).
simpl in |- *; auto with algebra.
unfold app_rel, group_quo_eq in |- *.
intros x x' y y' H' H'0; try assumption.
apply
 in_part_comp_l
  with
    (sgroup_law G x (sgroup_law G y (group_inverse G (sgroup_law G x' y'))));
 auto with algebra.
apply normal_com_in.
apply
 in_part_comp_l
  with
    (sgroup_law G
       (sgroup_law G y
          (sgroup_law G (group_inverse G y') (group_inverse G x'))) x);
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G
       (sgroup_law G (sgroup_law G y (group_inverse G y'))
          (group_inverse G x')) x); auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G (sgroup_law G y (group_inverse G y'))
       (sgroup_law G (group_inverse G x') x)); auto with algebra.
intros x y z; try assumption.
simpl in |- *; auto with algebra.
unfold app_rel, group_quo_eq in |- *.
apply
 in_part_comp_l
  with
    (sgroup_law G (sgroup_law G (sgroup_law G x y) z)
       (sgroup_law G (group_inverse G (sgroup_law G y z)) (group_inverse G x)));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G (sgroup_law G (sgroup_law G x y) z)
       (sgroup_law G (sgroup_law G (group_inverse G z) (group_inverse G y))
          (group_inverse G x))); auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G (sgroup_law G x (sgroup_law G y z))
       (sgroup_law G (group_inverse G z)
          (sgroup_law G (group_inverse G y) (group_inverse G x))));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G x
       (sgroup_law G (sgroup_law G y z)
          (sgroup_law G (group_inverse G z)
             (sgroup_law G (group_inverse G y) (group_inverse G x)))));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G x
       (sgroup_law G y
          (sgroup_law G z
             (sgroup_law G (group_inverse G z)
                (sgroup_law G (group_inverse G y) (group_inverse G x))))));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G x
       (sgroup_law G y
          (sgroup_law G (sgroup_law G z (group_inverse G z))
             (sgroup_law G (group_inverse G y) (group_inverse G x)))));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G x
       (sgroup_law G y
          (sgroup_law G (monoid_unit G)
             (sgroup_law G (group_inverse G y) (group_inverse G x)))));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G x
       (sgroup_law G y (sgroup_law G (group_inverse G y) (group_inverse G x))));
 auto with algebra.
apply
 in_part_comp_l
  with
    (sgroup_law G (sgroup_law G x y)
       (sgroup_law G (group_inverse G y) (group_inverse G x)));
 auto with algebra.
apply
 in_part_comp_l
  with (sgroup_law G (sgroup_law G x y) (group_inverse G (sgroup_law G x y)));
 auto with algebra.
apply in_part_comp_l with (monoid_unit G); auto with algebra.
simpl in |- *; auto with algebra.
unfold cart_eq, group_quo_eq in |- *.
intros x; try assumption.
apply in_part_comp_l with (sgroup_law G x (group_inverse G x));
 auto with algebra.
apply in_part_comp_l with (monoid_unit G); auto with algebra.
intros x y; try assumption.
simpl in |- *; auto with algebra.
unfold cart_eq, group_quo_eq in |- *.
intros H'; try assumption.
apply normal_com_in.
apply
 in_part_comp_l with (group_inverse G (sgroup_law G x (group_inverse G y)));
 auto with algebra.
intros x; try assumption.
simpl in |- *; auto with algebra.
unfold cart_eq, group_quo_eq in |- *.
apply
 in_part_comp_l
  with (sgroup_law G (sgroup_law G x (group_inverse G x)) (monoid_unit G));
 auto with algebra.
apply in_part_comp_l with (sgroup_law G x (group_inverse G x));
 auto with algebra.
apply in_part_comp_l with (monoid_unit G); auto with algebra.
Defined.
Set Implicit Arguments.
Unset Strict Implicit.

Definition group_quo_surj : Hom G group_quo.
apply (BUILD_HOM_GROUP (G:=G) (G':=group_quo) (ff:=fun x : G => x)).
intros x y; try assumption.
simpl in |- *; auto with algebra.
unfold cart_eq, group_quo_eq in |- *.
intros H'; try assumption.
apply in_part_comp_l with (sgroup_law G x (group_inverse G x));
 auto with algebra.
apply in_part_comp_l with (monoid_unit G); auto with algebra.
auto with algebra.
auto with algebra.
Defined.
End Def.
Hint Immediate normal_com_in: algebra.