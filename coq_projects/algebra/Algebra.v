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


Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Hom_module.
Section algebra_def.
Variable R : CRING.

Record algebra_on (Mod : MODULE R) : Type := 
  {algebra_bilinear_map : Hom_module Mod (Hom_module Mod Mod)}.

Record algebra : Type := 
  {algebra_carrier :> module R; algebra_on_def :> algebra_on algebra_carrier}.
Coercion Build_algebra : algebra_on >-> algebra.

Definition algebra_mult (A : algebra) (x y : A) : A :=
  algebra_bilinear_map A x y.

Record ring_algebra_on (A : algebra) : Type := 
  {ring_algebra_assoc :
    forall x y z : A,
    Equal (algebra_mult (algebra_mult x y) z)
      (algebra_mult x (algebra_mult y z));
   ring_algebra_unit : A;
   ring_algebra_unit_l :
    forall x : A, Equal (algebra_mult ring_algebra_unit x) x;
   ring_algebra_unit_r :
    forall x : A, Equal (algebra_mult x ring_algebra_unit) x}.

Record ring_algebra : Type := 
  {ring_algebra_algebra :> algebra;
   ring_algebra_on_def :> ring_algebra_on ring_algebra_algebra}.
Coercion Build_ring_algebra : ring_algebra_on >-> ring_algebra.
End algebra_def.
