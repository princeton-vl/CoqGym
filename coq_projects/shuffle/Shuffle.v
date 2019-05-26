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
(*                                                                          *)
(****************************************************************************)
(*                                Shuffle.v                                 *)
(****************************************************************************)
(* G. Huet - V5.8  Nov. 1994 *)
(*    ported V5.10 June 1995 *)

Require Import Bool.
Require Import Words.
Require Import Alternate.
Require Import Opposite.
Require Import Paired.


(***********************)
(* Shuffling two words *)
(***********************)

Inductive shuffle : word -> word -> word -> Prop :=
  | shuffle_empty : shuffle empty empty empty
  | shuffle_bit_left :
      forall u v w : word,
      shuffle u v w -> forall b : bool, shuffle (bit b u) v (bit b w)
  | shuffle_bit_right :
      forall u v w : word,
      shuffle u v w -> forall b : bool, shuffle u (bit b v) (bit b w).


(***********************)
(* The shuffling lemma *)
(***********************)

Lemma Shuffling :
 forall u v w : word,
 shuffle u v w ->
 forall b : bool,
 alt b u ->
 odd u /\
 (odd v /\ (alt (negb b) v -> paired w) /\ (alt b v -> paired_bet b w) \/
  even v /\
  (alt b v -> paired_odd_l b w) /\
  (alt (negb b) v -> paired_odd_r (negb b) w)) \/
 even u /\
 (odd v /\
  (alt (negb b) v -> paired_odd_r b w) /\ (alt b v -> paired_odd_l b w) \/
  even v /\ (alt b v -> paired_rot b w) /\ (alt (negb b) v -> paired w)).
Proof.
simple induction 1; intros.
(* 0. empty case *)
right.
split; auto.
right.
split; auto.
split; intro.
apply paired_rot_empty.
apply paired_empty.
(* 1. u before v *)
elim (alt_eq b0 b u0); trivial.
elim (H1 (negb b0)); intros.
(* 1.1. *) right.
elim H3; intros.
split; auto.
elim H5; intros.
elim H6; intros.
(* 1.1.1. *) left.
elim H8; intros. 
split; auto.
split; intro.
apply paired_odd_r_from_bet; auto.
apply paired_odd_l_intro; apply H9; rewrite (negb_elim b0); auto.
elim H6; intros.
elim H8; intros.
(* 1.1.2. *) right.
split; auto.
split; intro. 
apply paired_rot_bit; rewrite (negb_intro b0); apply H10;
 rewrite (negb_elim b0); auto.
apply paired_odd_l_elim; auto.
(* 1.2. *) left.
elim H3; intros.
split; auto.
elim H5; intros.
(* 1.2.1. *) left. 
elim H6; intros. 
elim H8; intros.
split; auto. 
split; intro. 
apply paired_odd_l_elim; auto.
apply paired_bet_bit; apply H9; rewrite (negb_elim b0); auto.
(* 1.2.2. *) right.
elim H6; intros. 
elim H8; intros.
split; auto.
split; intro.
apply paired_odd_l_intro; apply H10; rewrite (negb_elim b0); auto.
pattern b0 at 2 in |- *; rewrite (negb_intro b0).
apply paired_odd_r_from_rot; auto.
apply alt_neg_intro with b; trivial.
(* 2. v before u *)
elim (H1 b0); intros.
(* 2.1. *) left.
elim H3; intros.
split; auto.
elim H5; intros.
(* 2.1.1. *) right.
elim H6; intros.
elim H8; intros.
split; auto.
split; intro.
elim (alt_eq b0 b v0); trivial.
apply paired_odd_l_intro; apply H9; apply alt_neg_intro with b; auto.
elim (alt_eq (negb b0) b v0); trivial.
apply paired_odd_r_from_bet; rewrite (negb_elim b0); apply H10;
 apply alt_neg_elim with b; auto.
(* 2.1.2. *) left.
elim H6; intros.
elim H8; intros.
split; auto.
split; intro.
apply paired_odd_l_elim.
elim (alt_eq (negb b0) b v0); trivial.
rewrite (negb_elim b0).
apply H9.
rewrite (negb_intro b0).
apply alt_neg_intro with b; auto.
elim (alt_eq b0 b v0); trivial.
apply paired_bet_bit; apply H10; apply alt_neg_intro with b; auto.
(* 2.2. *) right.
elim H3; intros.
split; auto.
elim H5; intros.
(* 2.2.1. *) right.
elim H6; intros.
elim H8; intros.
split; auto.
split; intro.
elim (alt_eq b0 b v0); trivial.
apply paired_rot_bit; apply H9; apply alt_neg_intro with b; auto.
elim (alt_eq (negb b0) b v0); trivial.
apply paired_odd_l_elim.
rewrite (negb_elim b0); apply H10; rewrite (negb_intro b0);
 apply alt_neg_intro with b; auto.
(* 2.2.2. *) left.
elim H6; intros.
elim H8; intros.
split; auto.
split; intro.
elim (alt_eq (negb b0) b v0); trivial.
apply paired_odd_r_from_rot; apply H9; rewrite (negb_intro b0);
 apply alt_neg_intro with b; auto.
elim (alt_eq b0 b v0); trivial.
apply paired_odd_l_intro; apply H10; apply alt_neg_intro with b; auto.
trivial.
Qed.
