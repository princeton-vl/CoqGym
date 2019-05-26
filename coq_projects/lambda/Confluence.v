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
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                               Confluence.v                               *)
(*                                                                          *)
(*                                Gerard Huet                               *)
(*                                                                          *)
(* Developed in V5.8  January 1993                                          *)
(* Ported    to V5.10 January 1995                                          *)
(****************************************************************************)

Require Import Arith.
Require Import Terms.
Require Import Reduction.
Require Import Redexes.
Require Import Test.
Require Import Marks.
Require Import Substitution.
Require Import Residuals.
Require Import Simulation.
Require Import Cube.

(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.


Lemma lemma1 : confluence lambda par_red -> confluence lambda red.
Proof.
unfold all, confluence in |- *; intros.
cut (exists u : lambda, par_red y u /\ par_red z u).
simple induction 1.
intros u C; exists u; elim C; intros; split; apply par_red_red;
 trivial with arith.
apply H with x; apply red_par_red; trivial with arith.
Qed.


(* Strip lemmas *)

Definition strip :=
  forall x y : lambda,
  par_red x y ->
  forall z : lambda,
  par_red1 x z -> exists u : lambda, par_red1 y u /\ par_red z u.

Lemma strip_lemma_r : confluence lambda par_red1 -> strip.
Proof.
unfold strip in |- *; simple induction 2; intros.
elim H with M N z; trivial with arith.
intros u C; exists u; elim C; intros; split; trivial with arith.
apply one_step_par_red; trivial with arith.
elim (H2 z H5); intros.
elim H6; intros.
elim (H4 x0 H7); intros.
elim H9; intros.
exists x1; split; trivial with arith.
apply trans_par_red with x0; trivial with arith.
Qed.

Lemma strip_lemma_l : strip -> confluence lambda par_red.
Proof.
unfold confluence in |- *; simple induction 2; intros.
elim (H M z H2 N H1).
intros u C; exists u; elim C; intros; split; trivial with arith.
apply one_step_par_red; trivial with arith.
elim (H2 z H5); intros.
elim H6; intros.
elim (H4 x0 H7); intros.
elim H9; intros.
exists x1; split; trivial with arith.
apply trans_par_red with x0; trivial with arith.
Qed.

Lemma lemma2 : confluence lambda par_red1 -> confluence lambda par_red.
Proof.
intro C; unfold confluence in |- *; intros.
apply (strip_lemma_l (strip_lemma_r C) x); trivial with arith.
Qed.

(***************************************)
(* Parallel moves lemma and confluence *)
(***************************************)

Lemma parallel_moves : confluence lambda par_red1.
Proof.
red in |- *; intros M N R1 P R2.
elim (simulation M N); trivial with arith.
elim (simulation M P); trivial with arith.
intros V RV U RU.  
elim (paving U V (mark M) (mark N) (mark P)); trivial with arith.
intros UV C1; elim C1.
intros VU C2; elim C2.
intros UVW C3; elim C3; intros P1 P2.
exists (unmark UVW); split.
rewrite (inverse N).
apply Simulation.completeness with VU; trivial with arith.
rewrite (inverse P).
apply Simulation.completeness with UV; trivial with arith.
Qed.

Lemma confluence_parallel_reduction : confluence lambda par_red.
Proof.
apply lemma2; exact parallel_moves.
Qed.

Theorem confluence_beta_reduction : confluence lambda red.
Proof.
apply lemma1; exact confluence_parallel_reduction.
Qed.