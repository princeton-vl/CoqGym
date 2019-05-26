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
(*                                 Newman.v                                 *)
(****************************************************************************)

Require Import Relations.
Require Import Confluence.
Require Import Coherence.
Require Import Noetherian.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem Newman :
 forall (U : Type) (R : Relation U),
 Noetherian R -> Locally_confluent R -> Confluent R.
Proof.
intros U R H' H'0; red in |- *; intro x; red in |- *.
red in H'; generalize (H' x); intro H'1; elim H'1.
intros x0 H'2 H'3 y z H'4 H'5; clear H' H'1.
generalize (Rstar_cases (U:=U) (R:=R) (x:=x0) (y:=y)); intro h; lapply h;
 [ intro H'6; clear h | clear h; assumption ].
generalize (Rstar_cases (U:=U) (R:=R) (x:=x0) (y:=z)); intro h; lapply h;
 [ intro H'7; clear h | clear h; assumption ].
elim H'6;
 [ clear H'6; intro h
 | intro h; elim h; intros u h0; elim h0; intros H' H'1; clear H'6 h h0 ].
rewrite <- h; auto.
elim H'7;
 [ clear H'7; intro h
 | intro h; elim h; intros v h0; elim h0; intros H'6 H'8; clear H'7 h h0 ].
rewrite <- h; generalize coherent_symmetric; intro H_cs; red in H_cs; auto.
unfold Locally_confluent, locally_confluent, coherent in H'0.
generalize (H'0 x0 u v); intro h; lapply h;
 [ intro H'7; lapply H'7;
    [ intro h0; elim h0; intros t h1; elim h1; intros H'9 H'10;
       clear h H'7 h0 h1
    | clear h ]
 | clear h ]; auto.
clear H'0.
unfold coherent at 1 in H'3.
generalize (H'3 u); intro h; lapply h;
 [ intro H'0; generalize (H'0 y t); intro h0; lapply h0;
    [ intro H'7; lapply H'7;
       [ intro h1; elim h1; intros y1 h2; elim h2; intros H'11 H'12;
          clear h h0 H'7 h1 h2
       | clear h h0 ]
    | clear h h0 ]
 | clear h ]; auto.
generalize Rstar_transitive; intro H_Rst; red in H_Rst.
generalize (H'3 v); intro h; lapply h;
 [ intro H'7; generalize (H'7 y1 z); intro h0; lapply h0;
    [ intro H'13; lapply H'13;
       [ intro h1; elim h1; intros z1 h2; elim h2; intros H'14 H'15;
          clear h h0 H'13 h1 h2
       | clear h h0 ]
    | clear h h0 ]
 | clear h ]; auto.
red in |- *; (exists z1; split); auto.
apply H_Rst with y1; auto.
apply H_Rst with t; auto.
Qed.

(* $Id$ *)