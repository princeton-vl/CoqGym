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
Require Import List.

Definition Z_of_N (node : ad) :=
  match node with
  | N0 => 0%Z
  | Npos p => Zpos p
  end.

Definition test (be : bool_expr) :=
  match BDDof_bool_expr initBDDconfig initBDDneg_memo initBDDor_memo be with
  | ((bs, (share, counter)), (ad, _)) => (Z_of_N counter, Z_of_N ad)
  end.

Fixpoint testl (bel : list bool_expr) : list Z :=
  match bel with
  | nil => nil
  | be :: bel' =>
      match test be with
      | (counter, _) => counter :: testl bel'
      end
  end.

Definition Xor (be1 be2 : bool_expr) := Neg (Iff be1 be2).
Fixpoint Ands (bel : list bool_expr) : bool_expr :=
  match bel with
  | nil => One
  | be :: rest => match rest with
                  | nil => be
                  | _ => ANd be (Ands rest)
                  end
  end.
Fixpoint Ors (bel : list bool_expr) : bool_expr :=
  match bel with
  | nil => Zero
  | be :: rest => match rest with
                  | nil => be
                  | _ => Or be (Ors rest)
                  end
  end.
Fixpoint Iffs (bel : list bool_expr) : bool_expr :=
  match bel with
  | nil => One
  | be :: rest => match rest with
                  | nil => be
                  | _ => Iff be (Iffs rest)
                  end
  end.
Fixpoint even_len (l : list bool_expr) : bool :=
  match l with
  | nil => true
  | _ :: l' => negb (even_len l')
  end.
Definition Xors (bel : list bool_expr) :=
  (if even_len bel then Neg else fun be : bool_expr => be) (Iffs bel).