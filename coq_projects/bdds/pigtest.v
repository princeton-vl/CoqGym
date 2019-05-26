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


Require Import bdds.

Definition Z_of_N (node : ad) :=
  match node with
  | N0 => 0%Z
  | Npos p => Zpos p
  end.

Definition test (be : bool_expr) :=
  match BDDof_bool_expr initBDDconfig initBDDneg_memo initBDDor_memo be with
  | ((bs, (share, counter)), (ad, _)) => (Z_of_N counter, Z_of_N ad)
  end.

Definition v (n : nat) := Var (N_of_nat n).

Section Pigeons.
  Variable pigeons holes : nat.

  Definition holesp1 := holes + 1.

  Definition xi (hole pigeon : nat) := v (holes * pigeon + hole - holesp1).

  Section SomeHole.
    Variable pigeon : nat.

    Fixpoint is_in_some_hole_1 (maxhole : nat) : bool_expr :=
      match maxhole with
      | O => Zero
      | S O => xi 1 pigeon
      | S p => Or (xi maxhole pigeon) (is_in_some_hole_1 p)
      end.
    Definition is_in_some_hole := is_in_some_hole_1 holes.
  End SomeHole.

  Fixpoint each_pigeon_1 (pigeon : nat) : bool_expr :=
    match pigeon with
    | O => One
    | S O => is_in_some_hole 1
    | S p => ANd (is_in_some_hole pigeon) (each_pigeon_1 p)
    end.
  Definition each_pigeon_is_in_some_hole := each_pigeon_1 pigeons.

  Section NoMore.
    Variable hole : nat.

    Section G.
      Variable n : nat.

      Fixpoint g (pigeon : nat) : bool_expr :=
        match pigeon with
        | O => One
        | S O => Or (Neg (xi hole n)) (Neg (xi hole pigeon))
        | S p => ANd (Or (Neg (xi hole n)) (Neg (xi hole pigeon))) (g p)
        end.
    End G.

    Fixpoint f (maxpigeon : nat) : bool_expr :=
      match maxpigeon with
      | O => One
      | S O => One
      | S (S O) => g 2 1
      | S p => ANd (g maxpigeon p) (f p)
      end.
    Definition has_no_more_than_one_pigeon := f pigeons.
  End NoMore.

  Fixpoint no_hole_1 (maxhole : nat) : bool_expr :=
    match maxhole with
    | O => One
    | S O => has_no_more_than_one_pigeon 1
    | S p => ANd (has_no_more_than_one_pigeon maxhole) (no_hole_1 p)
    end.
  Definition no_hole_has_more_than_one_pigeon := no_hole_1 holes.

  Definition pb72 :=
    Neg (ANd each_pigeon_is_in_some_hole no_hole_has_more_than_one_pigeon).
End Pigeons.