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
(*                               Opposite.v                                 *)
(****************************************************************************)
(* G. Huet - V5.8  Nov. 1994 *)
(*    ported V5.10 June 1995 *)

Require Import Bool.
Require Import Words.
Require Import Alternate.


(************)
(* Opposite *)
(************)

Inductive opposite : word -> word -> Prop :=
    opp : forall (u v : word) (b : bool), opposite (bit b u) (bit (negb b) v).

Hint Resolve opp.

Lemma not_opp_empty_r : forall u : word, ~ opposite u empty.
Proof.
unfold not in |- *; intros u op.
inversion op.
Qed.

Lemma not_opp_empty_l : forall u : word, ~ opposite empty u.
Proof.
unfold not in |- *; intros u op.
inversion op.
Qed.

Lemma not_opp_same :
 forall (u v : word) (b : bool), ~ opposite (bit b u) (bit b v).
Proof.
unfold not in |- *; intros u v b op.
inversion op.
apply (no_fixpoint_negb b); trivial.
Qed.

Lemma alt_neg_opp :
 forall (u v : word) (b : bool),
 odd u -> alt b u -> odd v -> alt (negb b) v -> opposite u v.
Proof.
simple induction u.
intros v b odd_empty; absurd (odd empty); trivial.
intros b u' H v; elim v.
intros b' H1 H2 odd_empty.
absurd (odd empty); trivial.
intros b' v' H' b'' H1 H2 H3 H4.
elim (alt_eq (negb b'') b' v'); trivial.
elim (alt_eq b'' b u'); trivial.
Qed.

Lemma alt_not_opp :
 forall (u v : word) (b : bool), alt b u -> alt b v -> ~ opposite u v.
Proof.
simple induction u.
intros; apply not_opp_empty_l.
intros b u' H v; elim v.
intros; apply not_opp_empty_r.
intros b' v' H1 b'' H2 H3.
elim (alt_eq b'' b' v'); trivial.
elim (alt_eq b'' b u'); trivial.
apply not_opp_same.
Qed.
