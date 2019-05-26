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
(** Title "The category of fields." *)

Record field_on (R : ring) : Type := 
  {field_inverse_map : Map R R;
   field_inverse_r_prf :
    forall x : R,
    ~ Equal x (monoid_unit R) ->
    Equal (ring_mult x (Ap field_inverse_map x)) (ring_unit R);
   field_inverse_l_prf :
    forall x : R,
    ~ Equal x (monoid_unit R) ->
    Equal (ring_mult (Ap field_inverse_map x) x) (ring_unit R);
   field_unit_non_zero : ~ Equal (ring_unit R) (monoid_unit R):Prop}.

Record field : Type := 
  {field_ring :> ring; field_on_def :> field_on field_ring}.
Coercion Build_field : field_on >-> field.

Definition FIELD := full_subcat (C:=RING) (C':=field) field_ring.
