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
(*                                 Marks.v                                  *)
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

(* Translation from terms to redexes *)

Fixpoint mark (e : lambda) : redexes :=
  match e with
  | Ref n => Var n
  | Abs M => Fun (mark M)
  | App M N => Ap false (mark M) (mark N)
  end. 


(* Reverse translation : erasing the marks *)

Fixpoint unmark (e : redexes) : lambda :=
  match e with
  | Var n => Ref n
  | Fun U => Abs (unmark U)
  | Ap b U V => App (unmark U) (unmark V)
  end.

Lemma inverse : forall M : lambda, M = unmark (mark M).
Proof.
simple induction M; simpl in |- *; trivial; simple induction 1; trivial.
simple induction 1; trivial.
Qed.

Lemma comp_unmark_eq : forall U V : redexes, comp U V -> unmark U = unmark V.
Proof.
simple induction 1; simpl in |- *; trivial.
simple induction 2; trivial.
simple induction 2; simple induction 2; trivial.
Qed.

(* The converse is true, but not needed in the rest of the development *)
