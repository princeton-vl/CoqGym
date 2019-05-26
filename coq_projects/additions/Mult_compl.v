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

(* ---                     Mult_compl.v                                 ----*)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(*
   This file contains some lemmas on multiplication; it is an 
   extension of the module Mult.v *)

Require Import Arith.
Require Import Constants.
Require Import Le_lt_compl.

(* multiplication is monotonous *)

Lemma mult_le_l : forall a b c : nat, b <= c -> a * b <= a * c.
(******************************************)
Proof.
 simple induction a; simpl in |- *; [ auto with arith | intros ].
 apply plus_le_compat; auto with arith.
Qed.
Hint Resolve mult_le_l: arith.


(* multiplication is strictly monotonous *)

Lemma mult_lt_l : forall a b c : nat, 0 < a -> b < c -> a * b < a * c.
(******************************************)
Proof.
 simple induction a.
 intros; absurd (0 < 0); auto with arith.
 intros; simpl in |- *.
 apply lt_le_trans with (c + n * b).
 rewrite (plus_comm b (n * b)); rewrite (plus_comm c (n * b));
  apply plus_lt_compat_l; auto with arith.
 apply plus_le_compat_l; auto with arith.
Qed.

Hint Resolve mult_lt_l: arith.

(* same properties at right *)

Lemma mult_le_r : forall a b c : nat, b <= c -> b * a <= c * a.
(*****************************************)
Proof.
 intros; rewrite (mult_comm b a); rewrite (mult_comm c a); auto with arith.
Qed.
Hint Resolve mult_le_r: arith.


Lemma mult_lt_r : forall a b c : nat, 0 < a -> b < c -> b * a < c * a.
(******************************************)
Proof.
 intros; rewrite (mult_comm b a); rewrite (mult_comm c a); auto with arith.
Qed.
Hint Resolve mult_lt_r: arith.


Lemma mult_inj_l : forall a b c : nat, a * c < b * c -> a < b.
(********************************************)
Proof.
 intros.
 case (le_or_lt b a); [ intro | auto with arith ].
 absurd (b * c <= a * c); auto with arith.
Qed.


Lemma mult_p_lt_qp : forall p q : nat, 0 < p -> one < q -> p < q * p.  
(************************************)
Proof.
 intros.
 rewrite mult_comm.
 pattern p at 1 in |- *; rewrite <- mult_1_r; auto with arith.
Qed.

Lemma mult_p_le_qp : forall p q : nat, 0 < q -> p <= q * p.
(************************************)
Proof.
 intros.
 pattern p at 1 in |- *; rewrite <- mult_1_r.
 rewrite <- (mult_comm p q); auto with arith.
Qed.

Hint Resolve mult_p_lt_qp mult_p_le_qp: arith.
 
Lemma mult_p_lt_pq : forall p q : nat, 0 < p -> one < q -> p < p * q.  
(***********************************)
Proof.
 intros; rewrite mult_comm; auto with arith.
Qed.


Lemma mult_p_le_pq : forall p q : nat, 0 < q -> p <= p * q.
(************************************)
Proof.
 intros; rewrite mult_comm; auto with arith.
Qed.

Hint Resolve mult_p_lt_pq mult_p_le_pq: arith.


(* exact quotient 
******************)


Lemma quotient_positive : forall q n n0 : nat, n = q * n0 -> 0 < n -> 0 < q.
(***************************************)
Proof.
 intros q n n0 H H0.
 case (lt_or_Zero q); [ auto with arith | intro H1 ].
 absurd (0 < q * n0).
 rewrite H1; simpl in |- *; auto with arith.
 rewrite <- H; auto with arith.
Qed.

Lemma quotient_gt_one : forall q n n0 : nat, n0 < n -> n = q * n0 -> one < q.
(*************************************************)
Proof.
 intros q n n0 H H0; case (one_cases q);
  [ auto with arith
  | simple induction 1; intro; absurd (n0 < n); auto with arith ].
 rewrite H0; rewrite H2; auto with arith.
 rewrite H0; rewrite H2; simpl in |- *; rewrite <- plus_n_O; auto with arith.
Qed.






