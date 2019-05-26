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


Require Import Eqdep_dec.
Require Export Field.
Require Export Q_order.


(*###########################################################################*)
(** The Filed Structure for Field Tactic *)
(*###########################################################################*)

Lemma Q_Ring_Theory :
    ring_theory Zero Qone Qplus Qmult Qminus Qopp (eq(A:=Q)).
  split; intros n m p || intros n m || intros n; solve
   [ first
      [ apply Qplus_sym
      | apply Qplus_assoc
      | apply Qmult_sym
      | apply Qmult_assoc
      | apply Qplus_zero_left
      | apply Qmult_one_left
      | apply Q_opp_def
      | apply Q_distr_left
      | reflexivity ]].
Defined.

Lemma Qinv_defT : forall n : Q, n <> Zero -> Qmult (Qinv n) n = Qone.
Proof.
 intros n Hn; rewrite Qmult_sym; apply Qinv_def; intro;
  apply Hn; assumption.
Defined.

Lemma QField :
  field_theory Zero Qone Qplus Qmult Qminus Qopp Qdiv Qinv (eq(A:=Q)).
constructor.
 apply Q_Ring_Theory.
 discriminate.
 reflexivity.
 exact Qinv_defT.
Defined.

Ltac isQcst t :=
  match t with
    Zero => true
  | Qpos ?p => isQcst p
  | Qneg ?p => isQcst p
  | nR ?p => isQcst p
  | dL ?p => isQcst p
  | One => true
  | Qone => true
  | _ => false
  end.
Ltac Qcst t :=
  match isQcst t with
  | true => t
  | _ => InitialRing.NotConstant
  end.
 
Add Field Qfield : QField (decidable Q_eq_prop, constants [Qcst]).

Definition not_eq2eqT (A : Set) (x y : A) (H1 : x <> y) : 
  x <> y := fun H2 : x = y => H1 (H2).


Ltac Field := field.
