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

Fixpoint A_bound (n bound : nat) {struct bound} : bool_expr :=
  match bound with
  | O => v n
  | S bound' => Iff (v (n - bound)) (A_bound n bound')
  end.

Definition A (n : nat) := A_bound n n.

Fixpoint U_bound (n bound : nat) {struct bound} : bool_expr :=
  match bound with
  | O => A n
  | S bound' => Iff (v (n - bound')) (U_bound n bound')
  end.

Definition U (n : nat) := U_bound n (S n).