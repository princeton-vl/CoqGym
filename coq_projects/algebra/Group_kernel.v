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
Require Export Group_util.
Require Export Group_quotient.
Require Export Parts2.
(** Title "Kernel and image of a group homomorphism." *)
Section Def.
Variable G G' : GROUP.
Variable f : Hom G G'.

Definition kernel_part : part_set G.
apply
 (Build_Predicate (E:=G)
    (Pred_fun:=fun x : G => Equal (f x) (monoid_unit G'))).
red in |- *.
intros x y H' H'0; try assumption.
apply Trans with (Ap (sgroup_map (monoid_sgroup_hom f)) x); auto with algebra.
Defined.

Definition Ker : subgroup G.
apply (BUILD_SUB_GROUP (G:=G) (H:=kernel_part)).
simpl in |- *.
intros x y H' H'0; try assumption.
apply
 Trans
  with
    (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (Ap (sgroup_map (monoid_sgroup_hom f)) y)); 
 auto with algebra.
apply Trans with (sgroup_law G' (monoid_unit G') (monoid_unit G'));
 auto with algebra.
simpl in |- *.
auto with algebra.
simpl in |- *.
intros x H'; try assumption.
apply Trans with (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) x));
 auto with algebra.
apply Trans with (group_inverse _ (monoid_unit G')); auto with algebra.
Defined.

Definition coKer : subgroup G'.
apply (BUILD_SUB_GROUP (G:=G') (H:=image f (full G))).
intros x y H' H'0; try assumption.
elim H'0; intros x0 E; elim E; intros H'1 H'2; try exact H'2; clear E H'0.
elim H'; intros x1 E; elim E; intros H'0 H'3; try exact H'3; clear E H'.
exists (sgroup_law _ x1 x0); split; [ try assumption | idtac ].
apply
 Trans
  with
    (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom f)) x1)
       (Ap (sgroup_map (monoid_sgroup_hom f)) x0)); 
 auto with algebra.
simpl in |- *.
exists (monoid_unit G); auto with algebra.
simpl in |- *.
intros x H'; try assumption.
elim H'; intros x0 E; elim E; intros H'0 H'1; try exact H'1; clear E H'.
exists (group_inverse _ x0); split; [ try assumption | idtac ].
apply
 Trans with (group_inverse G' (Ap (sgroup_map (monoid_sgroup_hom f)) x0));
 auto with algebra.
Defined.

Lemma kernel_normal : normal Ker.
red in |- *.
simpl in |- *.
intros x y H'; try assumption.
apply
 Trans
  with
    (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (Ap (sgroup_map (monoid_sgroup_hom f))
          (sgroup_law G y (group_inverse G x)))); auto with algebra.
apply
 Trans
  with
    (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) y)
          (Ap (sgroup_map (monoid_sgroup_hom f)) (group_inverse G x))));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) y)
          (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) x))));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (sgroup_law _ (monoid_unit G')
          (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) x))));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)));
 auto with algebra.
Qed.
Set Strict Implicit.
Unset Implicit Arguments.

Definition group_quo_ker := group_quo G Ker kernel_normal.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma Ker_prop : forall x : G, in_part x Ker -> Equal (f x) (monoid_unit G').
auto with algebra.
Qed.

Lemma Ker_prop_rev :
 forall x : G, Equal (f x) (monoid_unit G') -> in_part x Ker.
auto with algebra.
Qed.

Lemma coKer_prop : forall x : G, in_part (f x) coKer.
simpl in |- *.
intros x; exists x; split; [ idtac | try assumption ]; auto with algebra.
Qed.
End Def.
Hint Resolve kernel_normal Ker_prop coKer_prop: algebra.