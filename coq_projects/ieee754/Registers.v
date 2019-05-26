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


(********************************************************)
(* Une  axiomatisation en coq de la norme IEEE 754 	*)
(* Module Registersv :    				*)
(*   registres machines (vecteurs de bits) 		*)
(* un plan d'ensemble se trouve dans le fichier README 	*)
(* Patrick Loiseleur, avril 1997			*)
(********************************************************)

Require Import Bool.
Require Import Omega.

Section registers.

(* The type (register n) represents integers who can write with n binary
  digits, i.e integers beetween 0 and 2^n - 1. The least significative 
  digit is on top :
    (regS true (regS true (regS false regO))) is 011 (binary) or 3 
    (regS false (regS false (regS true regO))) is 100 (binary) or 4
*)

Inductive register : nat -> Set :=
  | regO : register 0
  | regS : forall m : nat, bool -> register m -> register (S m).

(* 0 and max number represented by a register number *)

Definition register_zero :=
  nat_rec register regO (fun m : nat => regS m false).
Definition register_max := nat_rec register regO (fun m : nat => regS m true).
Fixpoint is_register_zero (n : nat) (x : register n) {struct x} : bool :=
  match x with
  | regO => true
  | regS m b y => if b then false else is_register_zero m y
  end.
Definition is_register_max (n : nat) (x : register n) :=
  match x with
  | regO => true
  | regS m b y => if b then is_register_zero m y else false
  end.

(*******
(* Decidable equality on registers *)
Fixpoint eq_register[n:nat; x:(register n); m:nat; y:(register m)] : bool :=
  Cases x y of
    regO regO => true
  | (regS n' bx x') (regS m' by y') => 
      (andb (eqb bx by) (eq_register n' x' m' y'))
  | _ _ => false
  end.
(* Egality of registers of same lenght *)
Definition eq_reg := [n:nat][x,y:(register n)](eq_register n x n y).

(* Alphabetic order on registers *)
Fixpoint lt_register[n:nat; x:(register n); m:nat; y:(register m)] : bool :=
  Cases x y of
    regO regO => false
  | (regS n' bx x') (regS m' by y') => 
      (orb (ifb bx false by) (lt_register n' x' m' y'))
  | regO (regS m' by y') => true
  | (regS n' bx x') regO => false
  end.
(* Order on registers of same lenght *)
Definition lt_reg := [n:nat][x,y:(register n)](lt_register n x n y).
********)

Fixpoint entier_of_register (n : nat) (x : register n) {struct x} : N :=
  match x with
  | regO => 0%N
  | regS m b y =>
      if b
      then Ndouble_plus_one (entier_of_register m y)
      else Ndouble (entier_of_register m y)
  end.
Definition Z_of_register (n : nat) (x : register n) :=
  BinInt.Z_of_N (entier_of_register n x).

(********
Lemma eq_register_correct : (n:nat)(x:(register n))(m:nat)(y:(register m))
  (eq_register n x m y)=(Case (%(Z_of_register n x) ?= (Z_of_register m y)) 
      	       	       	   of true false false end).
Lemma lt_register_correct : (n:nat)(x:(register n))(m:nat)(y:(register m))
  (lt_register n x m y)=(Case (%(Z_of_register n x) ?= (Z_of_register m y)) 
      	       	       	   of false true false end).
*********)

Definition sign_of (b : bool) := if b then 1%Z else (-1)%Z.

(* This function only reads the n less significative bits of x, or
  all bits of x if x has less than n digits. *)
(* In normal use of this function, we've always x < 2^n or
  x = 2^n + y when y<2^n *)

Fixpoint register_of_pos (n : nat) (x : positive) {struct x} : 
 register n :=
  match n as x return (register x) with
  | O => regO
  | S m =>
      match x with
      | xH => regS m true (register_zero m)
      | xI y => regS m true (register_of_pos m y)
      | xO y => regS m false (register_of_pos m y)
      end
  end.
Definition register_of_entier (n : nat) (x : N) :=
  match x return (register n) with
  | N0 => register_zero n
  | Npos p => register_of_pos n p
  end.
Definition register_of_Z (n : nat) (z : Z) : register n :=
  register_of_entier n (BinInt.Zabs_N z).

(******************************************************
*** Need the power of two
Lemma register_of_entier_bij1 : 
  (n:nat)(x:entier) (% x < (two_puiss_nat n)) ->
    (entier_of_register n (register_of_entier n x))=x.

###################################################################
Induction n;  
[ Destruct x; Normalize; Intros; Discriminate H
| Intros n0 HR; Destruct x; Intros; Simpl;
  [ Cut (% (POS p) < (two_puiss_nat n0));
    [ Intro Hp; Rewrite (HR p Hp); Reflexivity
    | Rewrite (POS_xI p) in H; Rewrite (two_puiss_nat_S n0) in H; Omega]
  |  Cut (% (POS p) < (two_puiss_nat n0));
    [ Intro Hp; Rewrite (HR p Hp); Reflexivity
    | Rewrite (POS_xO p) in H; Rewrite (two_puiss_nat_S n0) in H; Omega]
  | Replace (Z_of_register n0 (register_zero n0)) with `0`;
    [ Reflexivity
    | Elim n0; [ Trivial | Simpl; Intros n1 HZ; Rewrite <- HZ; Trivial ]]]
].
Save.
*********************************************)

Lemma register_of_entier_bij2 :
 forall (n : nat) (x : register n),
 register_of_entier n (entier_of_register n x) = x.

simple induction x;
 [ reflexivity
 | intros m b r; elim b;
    [ simpl in |- *; unfold Ndouble_plus_one in |- *;
       elim (entier_of_register m r); intros; rewrite <- H; 
       reflexivity
    | simpl in |- *; unfold Ndouble in |- *; elim (entier_of_register m r);
       intros; rewrite <- H; reflexivity ] ].
Qed.

Fixpoint register_compare (n : nat) (x : register n) 
 (m : nat) (y : register m) {struct y} : Datatypes.comparison :=
  match x with
  | regO => if is_register_zero m y then Datatypes.Eq else Datatypes.Lt
  | regS n' b_x x' =>
      match y with
      | regO => if is_register_zero n x then Datatypes.Eq else Datatypes.Gt
      | regS m' b_y y' =>
          match register_compare n' x' m' y' with
          | Datatypes.Eq =>
              if b_x
              then if b_y then Datatypes.Eq else Datatypes.Gt
              else if b_y then Datatypes.Lt else Datatypes.Eq
          | Datatypes.Gt => Datatypes.Gt
          | Datatypes.Lt => Datatypes.Lt
          end
      end
  end.

Definition reg_compare (n : nat) (x y : register n) :=
  register_compare n x n y.

(*****
Theorem register_compare_correct :
  (n:nat)(x:(register n))(m:nat)(y:(register m))
  (Zcompare (Z_of_register n x) (Z_of_register m y))=
  (register_compare n x m y).
Induction x; Induction y; Simpl; Auto.
*******)

End registers.
