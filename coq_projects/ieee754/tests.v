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


Require Import IEEE.

Definition t := Single.

Definition m := Rounding_nearest.

Definition test_add (x y : diadic) :=
  (Dadd x y,
  diadic_of_abstract t
    (fst
       (abstract_add t m (abstract_of_diadic t m x)
          (abstract_of_diadic t m y)))).

Definition verif (x y : diadic) := let (s1, s2) := test_add x y in Deq s1 s2.

Definition t1 := Diadic 10456 0.
Definition t2 := Diadic 10456 1.