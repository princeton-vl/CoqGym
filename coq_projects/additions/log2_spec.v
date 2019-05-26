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

(* -----                          log2_spec.v                          ---- *)

(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


Require Import Arith.
Require Import Peano_dec.
Require Import Constants.
Require Import Mult_compl.
Require Import Wf_nat. 
Require Import euclid.
Require Import Le_lt_compl.
Require Import shift.
Require Import Compare_dec.
Require Import two_power.

(* specification of logarithm (base 2) *)
(***************************************)
Definition log2_spec (n0 : nat) :=
  {l : nat & 
  {n0 = two_power l} + {two_power l < n0 /\ n0 < two_power (S l)}}.


Section applications.
 Variable log2 : forall n : nat, 0 < n -> log2_spec n.
 
 (* logarithm by excess *)
 (***********************)
 
 Lemma ceiling_log2 :
  forall n : nat,
  one < n -> {l : nat | two_power (pred l) < n /\ n <= two_power l}.
 
 (**********************************************)
 Proof.
 refine
  (fun n _ =>
   match log2 n _ with
   | existS l b =>
       match b with
       | left e => exist _ l _
       | right a => exist _ (S l) _
       end
   end).
 auto with arith.
(*
 Realizer [n:nat]<nat>let (l:nat;b:bool)=(log2 n) 
           in <nat> if b then l else (S l).
  Program_all.
*)
  rewrite e; split.
  apply two_power_mono.
  cut (0 < l).
  generalize l; induction  l as [| l Hrecl]; auto with arith.
  case (lt_or_Zero l); [ auto with arith | intro eg ].
  absurd (one < n);
   [ rewrite e; rewrite eg; simpl in |- *; auto with arith
   | auto with arith ].
  auto with arith.
  unfold pred in |- *; elim a; auto with arith.
 Qed.
 
 
 (* logarithm by default *)
 
 Lemma floor_log2 :
  forall n : nat,
  0 < n -> {l : nat | two_power l <= n /\ n < two_power (S l)}.
 (**************************************************************)
 Proof.
 refine (fun n _ => match log2 n _ with
                    | existS l b => exist _ l _
                    end).
 auto with arith.

(*
 Realizer [n:nat]<nat>let (l:nat;b:bool)=(log2 n) in  l .
  Program_all.
*)
  elim b; intro.
  rewrite a; split; auto with arith.
  elim b0; auto with arith.
 Qed.
End applications.