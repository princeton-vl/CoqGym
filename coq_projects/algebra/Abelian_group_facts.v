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
Require Export Abelian_group_cat.
Require Export Group_facts.
(** Title "Lemmas on abelian groups, monoids, semi-groups." *)
Section Sgroup.
Variable S : ABELIAN_SGROUP.

Lemma ABELIAN_SGROUP_com :
 forall x y : S, Equal (sgroup_law _ x y) (sgroup_law _ y x).
exact (abelian_sgroup_com_prf S).
Qed.

Lemma ABELIAN_SGROUP_permute :
 forall x y z : S,
 Equal (sgroup_law _ x (sgroup_law _ y z))
   (sgroup_law _ y (sgroup_law _ x z)).
intros x y z; try assumption.
apply Trans with (sgroup_law S (sgroup_law S x y) z); auto with algebra.
apply Trans with (sgroup_law S (sgroup_law S y x) z); auto with algebra.
apply SGROUP_comp; auto with algebra.
apply ABELIAN_SGROUP_com.
Qed.

Lemma ABELIAN_SGROUP4 :
 forall x y z t : S,
 Equal (sgroup_law _ (sgroup_law _ x y) (sgroup_law _ z t))
   (sgroup_law _ (sgroup_law _ x z) (sgroup_law _ y t)).
intros x y z t; try assumption.
apply Trans with (sgroup_law S x (sgroup_law S y (sgroup_law S z t)));
 auto with algebra.
apply Trans with (sgroup_law S x (sgroup_law S (sgroup_law S y z) t));
 auto with algebra.
apply Trans with (sgroup_law S x (sgroup_law S (sgroup_law S z y) t));
 auto with algebra.
apply SGROUP_comp; auto with algebra.
apply SGROUP_comp; auto with algebra.
apply ABELIAN_SGROUP_com.
apply Trans with (sgroup_law S x (sgroup_law S z (sgroup_law S y t)));
 auto with algebra.
Qed.
End Sgroup.
Hint Immediate ABELIAN_SGROUP_com ABELIAN_SGROUP_permute ABELIAN_SGROUP4:
  algebra.
Section Monoid.
Variable M : ABELIAN_MONOID.

Lemma ABELIAN_MONOID_com :
 forall x y : M, Equal (sgroup_law _ x y) (sgroup_law _ y x).
change
  (forall x y : M:ABELIAN_SGROUP, Equal (sgroup_law _ x y) (sgroup_law _ y x))
 in |- *; auto with algebra.
Qed.

Lemma ABELIAN_MONOID_permute :
 forall x y z : M,
 Equal (sgroup_law _ x (sgroup_law _ y z))
   (sgroup_law _ y (sgroup_law _ x z)).
change
  (forall x y z : M:ABELIAN_SGROUP,
   Equal (sgroup_law _ x (sgroup_law _ y z))
     (sgroup_law _ y (sgroup_law _ x z))) in |- *; 
 auto with algebra.
Qed.

Lemma ABELIAN_MONOID4 :
 forall x y z t : M,
 Equal (sgroup_law _ (sgroup_law _ x y) (sgroup_law _ z t))
   (sgroup_law _ (sgroup_law _ x z) (sgroup_law _ y t)).
change
  (forall x y z t : M:ABELIAN_SGROUP,
   Equal (sgroup_law _ (sgroup_law _ x y) (sgroup_law _ z t))
     (sgroup_law _ (sgroup_law _ x z) (sgroup_law _ y t))) 
 in |- *; auto with algebra.
Qed.
End Monoid.
Hint Immediate ABELIAN_MONOID_com ABELIAN_MONOID_permute ABELIAN_MONOID4:
  algebra.
Section Group.
Variable G : ABELIAN_GROUP.

Lemma ABELIAN_GROUP_com :
 forall x y : G, Equal (sgroup_law _ x y) (sgroup_law _ y x).
change
  (forall x y : G:ABELIAN_SGROUP, Equal (sgroup_law _ x y) (sgroup_law _ y x))
 in |- *; auto with algebra.
Qed.

Lemma ABELIAN_GROUP_permute :
 forall x y z : G,
 Equal (sgroup_law _ x (sgroup_law _ y z))
   (sgroup_law _ y (sgroup_law _ x z)).
change
  (forall x y z : G:ABELIAN_SGROUP,
   Equal (sgroup_law _ x (sgroup_law _ y z))
     (sgroup_law _ y (sgroup_law _ x z))) in |- *; 
 auto with algebra.
Qed.

Lemma ABELIAN_GROUP4 :
 forall x y z t : G,
 Equal (sgroup_law _ (sgroup_law _ x y) (sgroup_law _ z t))
   (sgroup_law _ (sgroup_law _ x z) (sgroup_law _ y t)).
change
  (forall x y z t : G:ABELIAN_SGROUP,
   Equal (sgroup_law _ (sgroup_law _ x y) (sgroup_law _ z t))
     (sgroup_law _ (sgroup_law _ x z) (sgroup_law _ y t))) 
 in |- *; auto with algebra.
Qed.
End Group.
Hint Immediate ABELIAN_GROUP_com ABELIAN_GROUP_permute ABELIAN_GROUP4:
  algebra.