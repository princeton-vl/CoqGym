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
(*                                  Test.v                                  *)
(****************************************************************************)

(* Arithmetic tests *)

Require Import Arith.

(* Pattern-matching lemmas for comparing 2 naturals 
   Similar to lemmas in Compare_dec *)

Definition test : forall n m : nat, {n <= m} + {n > m}.
Proof.
simple induction n; simple induction m; simpl in |- *; auto with arith.
intros m' H'; elim (H m'); auto with arith.
Defined.
(* Transparent test. *)

Definition le_lt : forall n m : nat, n <= m -> {n < m} + {n = m}.
Proof.
simple induction n; simple induction m; simpl in |- *; auto with arith.
intros m' H1 H2; elim (H m'); auto with arith.
Defined.
(* Transparent le_lt. *)

Definition compare : forall n m : nat, {n < m} + {n = m} + {n > m}.
Proof.
intros n m; elim (test n m); auto with arith.
left; apply le_lt; trivial with arith.
Defined.

(* Transparent compare. *)


