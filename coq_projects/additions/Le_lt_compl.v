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

(*                              Le_lt_compl.v                               *)

(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* 
 This file gives some additionnal lemmas to the modules
Le and Lt of the distribution: ($COQTH/ARITH/[Le,Lt] )
 
 Please notice that some lemmas and proofs use the constants
 one,two,three,four declared in the "Constants" module
*)

Require Import Arith.
Require Import Constants.


Lemma lt_or_Zero : forall q : nat, 0 < q \/ q = 0.
(************************************)
Proof.
  simple induction q; auto with arith.
Qed.

Lemma one_cases : forall q : nat, 1 < q \/ q = 0 \/ q = 1.
(************************************************)
Proof.
 simple induction q; auto with arith.
 simple induction n; auto with arith.
Qed.

Lemma enum1 : forall n : nat, n < two -> n = 0 \/ n = 1.
(******************************************)
Proof.
 intro n; case (one_cases n); [ idtac | auto with arith ].
 intros; absurd (two <= n); auto with arith.
Qed.


Lemma le5 :
 forall P : nat -> Prop,
 P 0 ->
 P one ->
 P two ->
 P three ->
 P four -> (forall n : nat, four < n -> P n) -> forall n : nat, P n.
(************************************)
Proof.
simple induction n;
 [ auto 2 with arith
 | simple induction n0;
    [ auto 2 with arith
    | simple induction n1;
       [ auto 2 with arith
       | simple induction n2;
          [ auto 2 with arith
          | simple induction n3;
             [ auto 2 with arith
             | intros; apply H4; unfold four in |- *; repeat apply lt_n_S;
                auto with arith ] ] ] ] ].
Qed.


Lemma enum4 :
 forall n : nat,
 n < S four -> n = 0 \/ n = one \/ n = two \/ n = three \/ n = four.
(*********************************************)
Proof.
 intro n; pattern n in |- *; apply le5; auto with arith.
 intros.
 absurd (n0 < S four); auto with arith.
Qed.


Lemma not_le_lt : forall n m : nat, ~ n <= m -> m < n.
(*******************************************)
Proof.
 intros; case (le_or_lt n m); [ intro | auto with arith ].
 elim (H H0).
Qed.
Hint Immediate not_le_lt: arith.


Lemma not_lt_le : forall n m : nat, ~ n < m -> m <= n.
(*******************************************)
Proof.
 intros; case (le_or_lt m n); [ auto with arith | intro ].
 elim (H H0).
Qed. 
Hint Immediate not_lt_le: arith.



Lemma lt_not_lt : forall n p : nat, n < p -> ~ p < S n.
(***************************************************)
Proof.
 auto with arith.
Qed.


Lemma lt_a_a_plus_b : forall a b : nat, 0 < b -> a < a + b.
(*******************************************************)
Proof.
 intros.
 pattern a at 1 in |- *; rewrite (plus_n_O a); auto with arith.
Qed.

Hint Resolve lt_a_a_plus_b: arith.



