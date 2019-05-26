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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)

(****************************************************************************)
(*                                 Terms.v                                  *)
(*                                                                          *)
(*                                Gerard Huet                               *)
(*                                                                          *)
(* Developed in V5.8  January 1993                                          *)
(* Ported    to V5.10 January 1995                                          *)
(****************************************************************************)

Require Import Arith.
Require Import Test.

(* Lambda terms with de Bruijn's indexes *)

Inductive lambda : Set :=
  | Ref : nat -> lambda
  | Abs : lambda -> lambda
  | App : lambda -> lambda -> lambda.


(* Lifting *)

Definition relocate (i k n : nat) :=
  match test k i with
  
      (* k<=i *) | left _ => n + i
   (* k>i  *) | _ => i
  end.



Fixpoint lift_rec (L : lambda) : nat -> nat -> lambda :=
  fun k n : nat =>
  match L with
  | Ref i => Ref (relocate i k n)
  | Abs M => Abs (lift_rec M (S k) n)
  | App M N => App (lift_rec M k n) (lift_rec N k n)
  end.

Definition lift (n : nat) (N : lambda) := lift_rec N 0 n.

(* Substitution *)


Definition insert_Ref (N : lambda) (i k : nat) :=
  match compare k i with
  
      (* k<i *) | inleft (left _) => Ref (pred i)
   (* k=i *) | inleft _ => lift k N
   (* k>i *) | _ => Ref i
  end.



Fixpoint subst_rec (L : lambda) : lambda -> nat -> lambda :=
  fun (N : lambda) (k : nat) =>
  match L with
  | Ref i => insert_Ref N i k
  | Abs M => Abs (subst_rec M N (S k))
  | App M M' => App (subst_rec M N k) (subst_rec M' N k)
  end.

Definition subst (N M : lambda) := subst_rec M N 0.





