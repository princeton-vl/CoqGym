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

(* ---                              euclid.v                          ----- *)

(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)
(* 
    Some lemmas about qb+r  ... (useful with euclidean division) 
*)


Require Import Arith.
Require Import Constants.
Require Import Le_lt_compl.
Require Import Mult_compl.

Lemma lt_b_qbr : forall b q r : nat, 0 < r -> 0 < q -> r < b -> b < q * b + r.
(***************************************************)     
Proof.
 intros. 
 apply le_lt_trans with (q * b).
 auto with arith.
 pattern (q * b) at 1 in |- *; rewrite plus_n_O; auto with arith.
Qed.

Hint Resolve lt_b_qbr: arith.

Lemma lt_q_qbr : forall b q r : nat, 0 < r -> one < b -> q < q * b + r.
(****************************************************)
Proof.
 simple induction q; [ auto with arith | intros ].
 apply lt_trans with (S n * b).
 auto with arith.
 pattern (S n * b) at 1 in |- *; rewrite (plus_n_O (S n * b));
  auto with arith.
Qed.
Hint Resolve lt_q_qbr: arith.



Lemma lt_q_qbr' : forall b q r : nat, 0 < q -> one < b -> q < q * b + r.
(****************************************************)
Proof.
 intros.
 apply lt_le_trans with (q * b); auto with arith.
Qed.

Hint Resolve lt_q_qbr': arith.


Lemma le_q_qbr : forall b q r : nat, 0 < b -> q <= q * b + r.
(***************************************************)
Proof.
 intros.
 apply le_trans with (q * b); auto with arith.
Qed.
  
Hint Resolve le_q_qbr: arith.


Lemma lt_O_q : forall b q r : nat, b < q * b + r -> 0 < r -> r < b -> 0 < q.
(***************************************************)
Proof.
 intros; case (lt_or_Zero q); [ auto with arith | intros ].
 absurd (b < r).
 apply lt_asym; auto with arith.
 replace r with (q * b + r); auto with arith.
 rewrite H2; simpl in |- *; auto with arith.
Qed.


