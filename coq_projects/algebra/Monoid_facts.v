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
Require Export Monoid_cat.
Section Lemmas.
Variable E : MONOID.

Lemma MONOID_unit_r : forall x : E, Equal (sgroup_law _ x (monoid_unit E)) x.
intros; apply (monoid_unit_r_prf E x).
Qed.

Lemma MONOID_unit_l : forall x : E, Equal (sgroup_law _ (monoid_unit E) x) x.
intros; apply (monoid_unit_l_prf E x).
Qed.

Lemma MONOID_unit_unique :
 forall e : E,
 (forall x : E, Equal (sgroup_law _ x e) x) ->
 (forall x : E, Equal (sgroup_law _ e x) x) -> Equal e (monoid_unit E).
intros e H' H'0; try assumption.
apply Trans with (sgroup_law _ e (monoid_unit E)); auto with algebra.
apply Sym.
apply MONOID_unit_r.
Qed.
Variable F : MONOID.
Variable f : Hom E F.

Lemma MONOID_hom_prop : Equal (f (monoid_unit E)) (monoid_unit F).
apply (monoid_hom_prf f).
Qed.
End Lemmas.
Hint Resolve MONOID_unit_r MONOID_unit_l MONOID_unit_unique MONOID_hom_prop:
  algebra.