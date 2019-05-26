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
Require Export Group_kernel.
(** Title "Factorisation of a group homomorphism: G -> G/Kerf -> coKerf -> G'." *)
Section Def.
Variable G G' : GROUP.
Variable f : Hom G G'.

Definition surj_group_quo_ker :
  Hom G (group_quo G (Ker f) (kernel_normal (G:=G) (G':=G') (f:=f))) :=
  group_quo_surj (kernel_normal (f:=f)).

Lemma surj_group_quo_ker_surjective : surjective surj_group_quo_ker.
red in |- *.
simpl in |- *.
unfold group_quo_eq, subtype_image_equal in |- *.
intros y; exists y; try assumption.
simpl in |- *.
apply Trans with (Ap (sgroup_map (monoid_sgroup_hom f)) (monoid_unit G));
 auto with algebra.
Qed.

Definition inj_coKer_group : Hom (coKer f:GROUP) G'.
apply (BUILD_HOM_GROUP (G:=coKer f) (G':=G') (ff:=inj_part (coKer f))).
simpl in |- *.
auto with algebra.
simpl in |- *.
auto with algebra.
simpl in |- *.
auto with algebra.
Defined.

Lemma inj_coKer_group_injective : injective inj_coKer_group.
exact (inj_part_injective (E:=G') (A:=coKer f)).
Qed.

Definition bij_group_quo_ker_coKer :
  Hom (group_quo G (Ker f) (kernel_normal (G:=G) (G':=G') (f:=f)):GROUP)
    (coKer f).
apply
 (BUILD_HOM_GROUP
    (G:=group_quo G (Ker f) (kernel_normal (G:=G) (G':=G') (f:=f)))
    (G':=coKer f)
    (ff:=fun x : G =>
         Build_subtype (P:=image (sgroup_map (monoid_sgroup_hom f)) (full G))
           (subtype_elt:=f x) (coKer_prop f x))).
simpl in |- *.
unfold group_quo_eq, subtype_image_equal in |- *.
simpl in |- *.
intros x y H'; try assumption.
apply
 GROUP_reg_right
  with (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) y));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (Ap (sgroup_map (monoid_sgroup_hom f)) (group_inverse G y)));
 auto with algebra.
apply
 Trans
  with
    (Ap (sgroup_map (monoid_sgroup_hom f))
       (sgroup_law G x (group_inverse G y))); auto with algebra.
apply Trans with (monoid_unit G'); auto with algebra.
simpl in |- *.
unfold group_quo_eq, subtype_image_equal in |- *.
simpl in |- *.
intros x y; try assumption.
exact (SGROUP_hom_prop f x y).
simpl in |- *.
unfold group_quo_eq, subtype_image_equal in |- *.
simpl in |- *.
auto with algebra.
Defined.

Lemma bij_group_quo_ker_coKer_bijective : bijective bij_group_quo_ker_coKer.
red in |- *.
split; [ try assumption | idtac ].
red in |- *.
simpl in |- *.
unfold group_quo_eq, subtype_image_equal in |- *.
simpl in |- *.
intros x y H'; try assumption.
apply
 Trans
  with
    (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (Ap (sgroup_map (monoid_sgroup_hom f)) (group_inverse G y)));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) y)));
 auto with algebra.
apply
 Trans
  with
    (sgroup_law G' (Ap (sgroup_map (monoid_sgroup_hom f)) x)
       (group_inverse _ (Ap (sgroup_map (monoid_sgroup_hom f)) x)));
 auto with algebra.
red in |- *.
intros y; try assumption.
elim y.
intros y' subtype_prf; try assumption.
elim subtype_prf.
intros x H'; try assumption.
elim H'; intros H'0 H'1; try exact H'0; clear H'.
exists x; try assumption.
Qed.

Theorem factor_group_hom :
 Equal f
   (comp_hom inj_coKer_group
      (comp_hom bij_group_quo_ker_coKer surj_group_quo_ker)).
simpl in |- *.
unfold Map_eq in |- *.
simpl in |- *.
auto with algebra.
Qed.
End Def.
Hint Resolve factor_group_hom bij_group_quo_ker_coKer_bijective
  inj_coKer_group_injective surj_group_quo_ker_surjective: algebra.