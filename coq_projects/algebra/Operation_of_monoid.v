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
Require Export Endo_set.
(** Title "Operation of a monoid on a set." *)
Section Def.
Variable M : MONOID.
Variable S : SET.

Definition operation := Hom M (Endo_SET S).
Variable op : operation.

Lemma operation_assoc :
 forall (x y : M) (s : S), Equal (op (sgroup_law _ x y) s) (op x (op y s)).
intros x y s; try assumption.
apply
 Trans
  with
    (Ap
       (sgroup_law (Endo_SET S) (Ap (sgroup_map (monoid_sgroup_hom op)) x)
          (Ap (sgroup_map (monoid_sgroup_hom op)) y)) s); 
 auto with algebra.
cut (Equal (op (sgroup_law _ x y)) (sgroup_law (Endo_SET S) (op x) (op y))).
auto with algebra.
apply (sgroup_hom_prf op).
Qed.

Lemma operation_unit : forall s : S, Equal (op (monoid_unit M) s) s.
intros s; try assumption.
apply Trans with (Id S s); auto with algebra.
cut (Equal (op (monoid_unit M)) (Id S)); auto with algebra.
apply Trans with (monoid_unit (Endo_SET S)).
generalize (monoid_hom_prf op).
unfold monoid_hom_prop in |- *.
auto with algebra.
auto with algebra.
Qed.
End Def.
Hint Resolve operation_assoc operation_unit: algebra.