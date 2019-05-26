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

(*                     --- shift.v ---                                      *)

(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* 
  Many programmers use left and right shifts in their code;
  so we found useful to provide some definitions and lemmas
  about these operations.
*)

Require Import Arith.
Require Import Peano_dec.
Require Import Constants.
Require Import Mult_compl.
Require Import Wf_nat. 
Require Import euclid.
Require Import Le_lt_compl.
Require Import Euclid.
Require Import Compare_dec.

Lemma plus_n_1 : forall n : nat, S n = n + 1.
Proof.
 intro n; rewrite <- (plus_n_Sm n 0); auto with arith.
Qed.


(* machine arithmetics *)

(* Left shift *)

Definition shift (n : nat) := two * n.
(************************************)

(* Right shift (and information on parity) *)

Lemma Unshift :
 forall n : nat, {m : nat &  {n = shift m} + {n = S (shift m)}}.
(*************************************************************)
Proof.
refine
 (fun n => match eucl_dev two _ n with
           | divex q r g e => existS _ q _
           end).
unfold two in |- *; auto.
elim (zerop r); intro e0; [ left | right ].
(*
 Realizer [n:nat]<nat*bool>let (q,r:nat)=(eucl_dev two n)
                in (q,(zerop r)).
 Program_all.
 *)
 rewrite e; rewrite e0; rewrite <- plus_n_O; unfold shift in |- *;
  auto with arith.
 cut (r = 1).
 intro eq1.
 rewrite e; rewrite eq1.
 unfold shift in |- *.
 rewrite <- plus_n_1; auto with arith.
 case (enum1 r).
 auto with arith.
 intro e'; absurd (0 < r); [ elim e'; auto with arith | auto with arith ].
 auto with arith.
Qed.


Lemma half_lt :
 forall a b : nat, 0 < b -> b = shift a \/ b = S (shift a) -> a < b.
(********************************************************)
Proof.
 intros; case (lt_or_Zero a); intro.
 case H0; intro.
 rewrite H2.
 unfold shift in |- *; apply mult_p_lt_qp; auto with arith.
 rewrite H2.
 rewrite plus_n_1.
 unfold shift in |- *.
 rewrite mult_comm; apply lt_q_qbr; auto with arith.
 rewrite H1; auto with arith.
Qed.
Hint Resolve half_lt: arith.









