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

(*  ---                        two_power.v                             ---  *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)



(* 
   The integer powers of 2 are fundamental in computer science;
   so we wrote this module, the results of which are used mainly
   in the "log2_spec" module.
*)



Require Import Arith.
Require Import Peano_dec.
Require Import Constants.
Require Import Mult_compl.
Require Import Le_lt_compl.


(* 2 at the n *)
(**************)

Fixpoint two_power (m : nat) : nat :=
  match m with
  | O => 1
  | S n => two * two_power n
  end.

Lemma zero_lt_pow : forall a : nat, 0 < two_power a.
(********************************************)
Proof.
 simple induction a; simpl in |- *.
 auto with arith.
 intros.
 apply lt_plus_trans; auto with arith.
Qed.
Hint Resolve zero_lt_pow: arith.


Lemma two_power_S : forall n : nat, two_power (S n) = two_power n * two.
(**************************************************)
Proof.
 intros; unfold two_power at 1 in |- *; rewrite mult_comm; auto with arith.
Qed.


Lemma two_power_S_lt : forall n : nat, two_power n < two_power (S n).
(***************************************************************)
Proof.
 intro; rewrite two_power_S.
 rewrite mult_comm; apply mult_p_lt_qp; auto with arith.
Qed.


Lemma two_power_mono : forall n p : nat, n < p -> two_power n < two_power p.
(*************************************************************)
Proof.
 simple induction 1.
 intros; apply two_power_S_lt; auto with arith.
 intros.
 apply lt_trans with (two_power m); auto with arith.
 apply two_power_S_lt; auto with arith.
Qed.


Lemma two_power_le : forall n p : nat, n <= p -> two_power n <= two_power p.
(**************************************************************)
Proof.
 intros n p H; case (le_lt_or_eq _ _ H); intro H1.
 apply lt_le_weak; apply two_power_mono; auto with arith.
 rewrite H1; auto with arith.
Qed.

Lemma two_power_monoR : forall n p : nat, two_power n < two_power p -> n < p.
(****************************************************************)
Proof.
 intros.
 apply not_le_lt.
 unfold not in |- *; intro.
 elim (lt_not_le (two_power n) (two_power p) H).
 case (le_lt_or_eq p n H0); intro.
 apply lt_le_weak.
 apply two_power_mono; auto with arith.
 auto with arith.
 rewrite H1; auto with arith.
Qed.


(* if 2^n < z <2^(n+1), then z cannot be a power of 2 ! *)
(*********************************************************)

Lemma holes_in_powers :
 forall n z : nat,
 two_power n < z -> z < two_power (S n) -> forall p : nat, z <> two_power p.
(**************************************************************)
Proof.
 unfold not in |- *; intros.
 cut (n < p).
 intro.
 cut (p < S n).
 intro.
 case (lt_not_lt n p); auto with arith.
 apply two_power_monoR.
 elim H1; auto with arith.
 apply two_power_monoR.
 elim H1; auto with arith.
Qed.


(* the intervals ]2^n,2^(n+1)[ are pairwise disjoint *)
(*****************************************************)

Lemma log2_unicity :
 forall n p z : nat,
 two_power n < z ->
 z < two_power (S n) -> two_power p < z -> z < two_power (S p) -> n = p.
Proof.
 intros.
 case (le_or_lt n p); intros.		                     
 case (le_lt_or_eq n p H3); intros.
 absurd (z < z).
 auto with arith.
 apply lt_trans with (two_power (S n)).
 auto with arith.
 apply le_lt_trans with (two_power p).
 apply two_power_le; auto with arith.
 auto with arith.
 auto with arith.
 absurd (z < z).
 auto with arith.
 apply lt_trans with (two_power (S p)).
 auto with arith.
 apply le_lt_trans with (two_power n).
 apply two_power_le; auto with arith.
 auto with arith.
Qed.