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
Require Export Sgroup_cat.
Section Lemmas.
Variable E : SGROUP.

Lemma SGROUP_assoc :
 forall x y z : E,
 Equal (sgroup_law _ (sgroup_law _ x y) z)
   (sgroup_law _ x (sgroup_law _ y z)).
intros x y z; try assumption.
apply (sgroup_assoc_prf E x y z); auto with algebra.
Qed.

Lemma SGROUP_comp :
 forall x x' y y' : E,
 Equal x x' -> Equal y y' -> Equal (sgroup_law _ x y) (sgroup_law _ x' y').
unfold sgroup_law in |- *; auto with algebra.
Qed.
Variable F : SGROUP.
Variable f : Hom E F.

Lemma SGROUP_hom_prop :
 forall x y : E, Equal (f (sgroup_law _ x y)) (sgroup_law _ (f x) (f y)).
intros x y; try assumption.
apply (sgroup_hom_prf f).
Qed.
End Lemmas.
Hint Resolve SGROUP_assoc SGROUP_comp SGROUP_hom_prop: algebra.