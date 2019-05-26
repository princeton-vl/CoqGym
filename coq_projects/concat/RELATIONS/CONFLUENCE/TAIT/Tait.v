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
(*                                 Coq V6.1                                 *)
(*                               Oct 1st 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                                  Tait.v                                  *)
(****************************************************************************)


Require Import Relations.
Require Import Confluence.
Require Import Coherence.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem Strip :
 forall (U : Type) (R : Relation U),
 Strongly_confluent R ->
 forall x b : U,
 Rstar R x b -> forall a : U, R x a -> exists z : U, Rstar R a z /\ R b z.
Proof.
intros U R H' x b H'0; elim H'0.
intros x0 a H'1; exists a; auto.
intros x0 y z H'1 H'2 H'3 a H'4.
red in H'.
generalize (H' x0 a y); intro h; lapply h;
 [ intro H'5; lapply H'5;
    [ intro h0; elim h0; intros t h1; elim h1; intros H'6 H'7;
       clear h H'5 h0 h1; try exact H'6
    | clear h ]
 | clear h ]; auto 10.
generalize (H'3 t); intro h; lapply h;
 [ intro h0; elim h0; intros z1 h1; elim h1; intros H'5 H'8; clear h h0 h1;
    try exact H'5
 | clear h ]; auto 10.
exists z1; split; [ idtac | assumption ].
apply Rstar_n with t; auto.
Qed.

Theorem Strong_confluence_confluence :
 forall (U : Type) (R : Relation U), Strongly_confluent R -> Confluent R.
Proof.
intros U R H'; red in |- *.
intro x; red in |- *; intros a b H'0.
unfold coherent at 1 in |- *.
generalize b; clear b.
elim H'0; clear H'0.
intros x0 b H'1; exists b; auto.
intros x0 y z H'1 H'2 H'3 b H'4.
generalize (Strip (U:=U) (R:=R)); intro h; lapply h;
 [ intro H'0; generalize (H'0 x0 b); intro h0; lapply h0;
    [ intro H'5; generalize (H'5 y); intro h1; lapply h1;
       [ intro h2; elim h2; intros z0 h3; elim h3; intros H'6 H'7;
          clear h h0 h1 h2 h3
       | clear h h0 h1 ]
    | clear h h0 ]
 | clear h ]; auto.
generalize (H'3 z0); intro h; lapply h;
 [ intro h0; elim h0; intros z1 h1; elim h1; intros H'8 H'9; clear h h0 h1
 | clear h ]; auto.
exists z1; split; auto.
apply Rstar_n with z0; auto.
Qed.

(* $Id$ *)