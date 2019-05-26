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
(*                               Alternate.v                                *)
(****************************************************************************)
(* G. Huet - V5.8  Nov. 1994 *)
(*    ported V5.10 June 1995 *)

Require Import Bool.
Require Import Words.

(*********************)
(* Alternating words *)
(*********************)

(* (alt b w) == w = [b ~b b ~b ...]  *)

Inductive alt : bool -> word -> Prop :=
  | alt_empty : forall b : bool, alt b empty
  | alt_bit : forall (b : bool) (w : word), alt (negb b) w -> alt b (bit b w).

Hint Resolve alt_empty alt_bit.

Lemma alt_neg_intro :
 forall (b b' : bool) (w : word), alt b (bit b' w) -> alt (negb b) w.
Proof.
intros b b' w al.
inversion al; trivial.
Qed.

Lemma alt_neg_elim :
 forall (b b' : bool) (w : word), alt (negb b) (bit b' w) -> alt b w.
Proof.
intros; rewrite (negb_intro b); apply alt_neg_intro with b'; trivial.
Qed.

Lemma alt_eq : forall (b b' : bool) (w : word), alt b (bit b' w) -> b = b'.
Proof.
intros b b' w al.
inversion al; trivial.
Qed.

Lemma alt_back :
 forall (b b' : bool) (w : word),
 alt b (bit b' w) -> b = b' /\ alt (negb b) w.
Proof.
intros; split.
apply alt_eq with w; trivial.
apply alt_neg_intro with b'; trivial.
Qed.

Inductive alternate (w : word) : Prop :=
    alter : forall b : bool, alt b w -> alternate w.

(* (alternate w) iff Exists b  (alt b w)  *)

(*********************************************)
(* Subwords of alternate words are alternate *)
(*********************************************)

Lemma alt_conc_l :
 forall u v w : word, conc u v w -> forall b : bool, alt b w -> alt b u.
Proof.
simple induction 1; auto; intros.
elim alt_back with b0 b w0.
intros eq A.
elim eq; auto.
trivial.
Qed.

Lemma alt_conc_r :
 forall u v w : word,
 conc u v w ->
 forall b : bool, alt b w -> odd u /\ alt (negb b) v \/ even u /\ alt b v.
Proof.
simple induction 1; intros.
right; split; intros; auto.
elim H1 with (negb b0).
rewrite (negb_elim b0); intro.
right; split; elim H3; auto.
intro; left; split; elim H3; auto.
apply alt_neg_intro with b; trivial.
Qed.

Lemma alt_conc :
 forall u v w : word, conc u v w -> alternate w -> alternate u /\ alternate v.
Proof.
simple induction 2; intros b ab; split.
apply alter with b; apply alt_conc_l with v w; trivial.
elim alt_conc_r with u v w b; intros; trivial.
elim H1; intros; apply alter with (negb b); trivial.
elim H1; intros; apply alter with b; trivial.
Qed. (* unused in Shuffle *)

