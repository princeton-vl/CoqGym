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
(*                               Conversion.v                               *)
(*                                                                          *)
(*                                Gerard Huet                               *)
(*                                                                          *)
(* Developed in V5.8  January 1993                                          *)
(* Ported    to V5.10 January 1995                                          *)
(****************************************************************************)

Require Import Terms.
Require Import Reduction.
Require Import Confluence.

Inductive conv1 : lambda -> lambda -> Prop :=
  | red1_conv : forall M N : lambda, red1 M N -> conv1 M N
  | exp1_conv : forall M N : lambda, red1 N M -> conv1 M N.

(* Beta conversion *)
Inductive conv : lambda -> lambda -> Prop :=
  | one_step_conv : forall M N : lambda, conv1 M N -> conv M N
  | refl_conv : forall M : lambda, conv M M
  | trans_conv : forall M N P : lambda, conv M N -> conv N P -> conv M P.

Lemma sym_conv : forall M N : lambda, conv M N -> conv N M.
Proof.
simple induction 1.
simple induction 1; intros; apply one_step_conv.
apply exp1_conv; trivial.
apply red1_conv; trivial.
intro; apply refl_conv; trivial.
intros; apply trans_conv with N0; trivial.
Qed.

Require Import Confluence.

Theorem Church_Rosser :
 forall M N : lambda, conv M N -> exists P : lambda, red M P /\ red N P.
Proof.
simple induction 1.
simple induction 1; intros.
exists N1; split; [ apply one_step_red; trivial | apply refl_red; trivial ].
exists M1; split; [ apply refl_red; trivial | apply one_step_red; trivial ].
intro M0; exists M0; split; apply refl_red; trivial.
intros; elim H1; intros P0 C0; elim H3; intros P1 C1; elim C0; elim C1;
 intros.
elim confluence_beta_reduction with N0 P0 P1; trivial.
intros Q C3; exists Q; elim C3; split.
apply trans_red with P0; trivial.
apply trans_red with P1; trivial.
Qed.
