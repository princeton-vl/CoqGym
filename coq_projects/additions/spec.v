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

(* ---                           spec.v                                 --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(* 
  This file presents the notations used by the "develop",
  "generation" and "main"  modules.

*)

Require Import monoid.
Require Import machine.
Require Import Constants.



(* The addition-chain algorithm uses three mutually  recursive
    functions for generating abstract machine code.
    In order to use the Program tactic, we treat them at the same time.
   First, we define the type of "procedure calls":
*)

Inductive Call : Set :=
  | Call_M : nat -> Call
  | Call_C : nat -> nat -> Call
  | Call_K : nat -> nat -> Call.
 

(* We define constraints on the parameters of procedure calls *)

Definition conform (c : Call) : Prop :=
  match c return Prop with
  | Call_M n =>
      (* Call_M n *)  0 < n
      (* Call_C n p *) 
  | Call_C n p => 1 < p /\ p < n
      (* Call_K n p *) 
  | Call_K n p => 0 < p /\ p < n
  end.

(*  The proposition (Spec C c) means
    "The code c is correct wrt the call C" 

     That is to say:
       A code for (Call_M p) leaves the stack unchanged,
       and replaces a value x in the register X by x^p.

       A code for (Call_C p q) does the same thing as (Call_M p),
       but we know that the value x^q is computed before x^p
       (2 <= q < p )
    
       A code for (Call_K p q) does  almost the same thing as
       (Call_C p q), except that the computation pushes x^q
       at the top of the stack.
*)


Inductive Spec : Call -> Code -> Prop :=
  | m_spec :
      forall (n : nat) (c : Code),
      (forall (M : Set) (MO : monoid M) (a : M) (s : Stack M),
       Exec M MO c (config M a s) = config M (power M MO a n) s) ->
      Spec (Call_M n) c
  | c_spec :
      forall (p q : nat) (c : Code),
      (forall (M : Set) (MO : monoid M) (a : M) (s : Stack M),
       Exec M MO c (config M a s) = config M (power M MO a p) s) ->
      Spec (Call_C p q) c
  | k_spec :
      forall (p q : nat) (c : Code),
      (forall (M : Set) (MO : monoid M) (a : M) (s : Stack M),
       Exec M MO c (config M a s) =
       config M (power M MO a p) (push M (power M MO a q) s)) ->
      Spec (Call_K p q) c.


(* code generation  for each call
*********************************)

Inductive gencode (c : Call) : Set :=
    gencode_intro : forall co : Code, Spec c co -> gencode c.


(* specification of the powering algorithm 
******************************************)

Inductive addchain_spec (n : nat) : Set :=
    addchain_spec_intro : gencode (Call_M n) -> addchain_spec n.



