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
Require Export Ring_cat.
(** Title "The category of integral domains." *)
Section Objects.

Definition idomain_prop (R : CRING) :=
  forall x y : R,
  ~ Equal x (monoid_unit R) ->
  ~ Equal y (monoid_unit R) -> ~ Equal (ring_mult x y) (monoid_unit R).

Record idomain_on (R : cring) : Type :=  {idomain_prf : idomain_prop R}.

Record idomain : Type := 
  {idomain_ring :> cring; idomain_on_def :> idomain_on idomain_ring}.
Coercion Build_idomain : idomain_on >-> idomain.

Definition INTEGRAL_DOMAIN :=
  full_subcat (C:=CRING) (C':=idomain) idomain_ring.
End Objects.