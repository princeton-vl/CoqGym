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
(*                                 Paired.v                                 *)
(****************************************************************************)
(* G. Huet - V5.8  Nov. 1994 *)
(*    ported V5.10 June 1995 *)

Require Import Bool.
Require Import Words.

(****************)
(* Paired words *)
(****************)

(* (paired w) ==  w = [b1 ~b1 b2 ~b2 ... bn ~bn] *)
Inductive paired : word -> Prop :=
  | paired_empty : paired empty
  | paired_bit :
      forall w : word,
      paired w -> forall b : bool, paired (bit (negb b) (bit b w)).

(* paired_odd_l b w == w = [b b1 ~b1 b2 ~b2 ... bn ~bn] *)
Definition paired_odd_l (b : bool) (w : word) := paired (bit (negb b) w).

Lemma paired_odd_l_intro :
 forall (b : bool) (w : word), paired w -> paired_odd_l b (bit b w).
Proof.
unfold paired_odd_l in |- *; intros.
apply paired_bit; trivial.
Qed.

Lemma paired_odd_l_elim :
 forall (b : bool) (w : word), paired_odd_l (negb b) w -> paired (bit b w).
Proof.
unfold paired_odd_l in |- *; intros.
rewrite (negb_intro b); trivial.
Qed.

(* paired_odd_r b w == w = [b1 ~b1 b2 ~b2 ... bn ~bn ~b] *)
Definition paired_odd_r (b : bool) (w : word) := paired (append w (single b)).

(* paired_rot b w == w = [b b2 ~b2 ... bn ~bn ~b] *)
Inductive paired_rot : bool -> word -> Prop :=
  | paired_rot_empty : forall b : bool, paired_rot b empty
  | paired_rot_bit :
      forall (b : bool) (w : word),
      paired_odd_r b w -> paired_rot b (bit b w).

Lemma paired_odd_r_from_rot :
 forall (w : word) (b : bool),
 paired_rot b w -> paired_odd_r b (bit (negb b) w).
Proof.
simple induction 1.
intro; unfold paired_odd_r in |- *; simpl in |- *.
unfold single in |- *; apply paired_bit.
apply paired_empty.
intros b0 b' w'; unfold paired_odd_r in |- *; intros.
simpl in |- *; apply paired_bit; auto.
Qed.

(* paired_bet b w == w = [b b2 ~b2 ... bn ~bn b] *)
Inductive paired_bet (b : bool) : word -> Prop :=
    paired_bet_bit :
      forall w : word, paired_odd_r (negb b) w -> paired_bet b (bit b w).

Lemma paired_odd_r_from_bet :
 forall (b : bool) (w : word),
 paired_bet (negb b) w -> paired_odd_r b (bit b w).
Proof.
intros b w pb.
rewrite (negb_intro b).
elim pb.
unfold paired_odd_r in |- *. (* Unfolds twice *)
intros; simpl in |- *.
apply paired_bit; trivial.
Qed.


(************)
(* Rotation *)
(************)

Definition rotate (w : word) : word :=
  match w with
  | empty => empty
  | bit b w => append w (single b)
  end.

Lemma paired_rotate :
 forall (w : word) (b : bool), paired_rot b w -> paired (rotate w).
Proof.
simple induction 1.
intro; simpl in |- *; apply paired_empty.
intros b' w'; simpl in |- *.
unfold paired_odd_r in |- *; trivial.
Qed.
