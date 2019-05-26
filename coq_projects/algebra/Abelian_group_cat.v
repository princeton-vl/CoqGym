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
(** Title "The categories of abelian semi-groups, monoids and groups." *)

Definition commutative (E : SET) (f : law_of_composition E) :=
  forall x y : E, Equal (f (couple x y)) (f (couple y x)).

Record abelian_sgroup_on (A : sgroup) : Type := 
  {abelian_sgroup_com_prf : commutative (sgroup_law_map A)}.

Record abelian_sgroup : Type := 
  {abelian_sgroup_sgroup :> sgroup;
   abelian_sgroup_on_def :> abelian_sgroup_on abelian_sgroup_sgroup}.
Coercion Build_abelian_sgroup : abelian_sgroup_on >-> abelian_sgroup.

Definition ABELIAN_SGROUP :=
  full_subcat (C:=SGROUP) (C':=abelian_sgroup) abelian_sgroup_sgroup.

Record abelian_monoid_on (M : monoid) : Type := 
  {abelian_monoid_abelian_sgroup :> abelian_sgroup_on M}.

Record abelian_monoid : Type := 
  {abelian_monoid_monoid :> monoid;
   abelian_monoid_on_def :> abelian_monoid_on abelian_monoid_monoid}.
Coercion Build_abelian_monoid : abelian_monoid_on >-> abelian_monoid.

Definition ABELIAN_MONOID :=
  full_subcat (C:=MONOID) (C':=abelian_monoid) abelian_monoid_monoid.

Record abelian_group_on (G : group) : Type := 
  {abelian_group_abelian_monoid :> abelian_monoid_on G}.

Record abelian_group : Type := 
  {abelian_group_group :> group;
   abelian_group_on_def :> abelian_group_on abelian_group_group}.
Coercion Build_abelian_group : abelian_group_on >-> abelian_group.

Definition ABELIAN_GROUP :=
  full_subcat (C:=GROUP) (C':=abelian_group) abelian_group_group.