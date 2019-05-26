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
(*                               Simulation.v                               *)
(*                                                                          *)
(*                                Gerard Huet                               *)
(*                                                                          *)
(* Developed in V5.8  January 1993                                          *)
(* Ported    to V5.10 January 1995                                          *)
(****************************************************************************)

(* Reduction of a term by a set of redexes *)

Require Import Arith.
Require Import Terms.
Require Import Reduction.
Require Import Redexes.
Require Import Test.
Require Import Marks.
Require Import Substitution.
Require Import Residuals.

(* Commuting mark and subst *)

Lemma mark_lift_rec :
 forall (M : lambda) (n k : nat),
 lift_rec_r (mark M) k n = mark (lift_rec M k n).
Proof.
simple induction M; simpl in |- *; intros.
elim (test k n); simpl in |- *; intros; trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma mark_lift :
 forall (M : lambda) (n : nat), lift_r n (mark M) = mark (lift n M).
Proof.
unfold lift in |- *; unfold lift_r in |- *; intros; apply mark_lift_rec.
Qed.

Lemma mark_subst_rec :
 forall (N M : lambda) (n : nat),
 subst_rec_r (mark M) (mark N) n = mark (subst_rec M N n).
Proof.
simple induction M; simpl in |- *; intros.
unfold insert_Var, insert_Ref in |- *.
elim (compare n0 n); intro H.
elim H; intro H'.
simpl in |- *; trivial.
rewrite (mark_lift N n0); trivial.
simpl in |- *; trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma mark_subst :
 forall M N : lambda, subst_r (mark M) (mark N) = mark (subst M N).
Proof.
unfold subst in |- *; unfold subst_r in |- *; intros; apply mark_subst_rec.
Qed.

(* residuals simulates par_red1 *)

Lemma simulation :
 forall M M' : lambda,
 par_red1 M M' -> exists V : redexes, residuals (mark M) V (mark M').
Proof.
simple induction 1; simpl in |- *; intros.
elim H1; intros V1 P1.
elim H3; intros V2 P2.
exists (Ap true (Fun V1) V2).
elim mark_subst; auto.
exists (Var n); trivial.
elim H1; intros V1 P1.
exists (Fun V1); auto.
elim H1; intros V1 P1.
elim H3; intros V2 P2.
exists (Ap false V1 V2); auto.
Qed.

(* Commuting unmark and subst *)

Lemma unmark_lift_rec :
 forall (U : redexes) (n k : nat),
 lift_rec (unmark U) k n = unmark (lift_rec_r U k n).
Proof.
simple induction U; simpl in |- *; intros.
elim (test k n); trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma unmark_lift :
 forall (U : redexes) (n : nat), lift n (unmark U) = unmark (lift_r n U).
Proof.
unfold lift in |- *; unfold lift_r in |- *; intros; apply unmark_lift_rec.
Qed.

Lemma unmark_subst_rec :
 forall (V U : redexes) (n : nat),
 subst_rec (unmark U) (unmark V) n = unmark (subst_rec_r U V n).
Proof.
simple induction U; simpl in |- *; intros.
unfold insert_Var, insert_Ref in |- *.
elim (compare n0 n); intro H; simpl in |- *; trivial.
elim H; trivial.
rewrite (unmark_lift V n0); trivial.
elim H; trivial.
elim H; elim H0; trivial.
Qed.

Lemma unmark_subst :
 forall U V : redexes, subst (unmark U) (unmark V) = unmark (subst_r U V).
Proof.
unfold subst in |- *; unfold subst_r in |- *; intros; apply unmark_subst_rec.
Qed.

Lemma completeness :
 forall U V W : redexes, residuals U V W -> par_red1 (unmark U) (unmark W).
Proof.
simple induction 1; simpl in |- *; auto.
intros; elim unmark_subst; auto.
Qed.


(**************************************************)
(* Reduction of a lambda term by a set of redexes *)
(**************************************************)

Definition reduction (M : lambda) (U : redexes) (N : lambda) :=
  residuals (mark M) U (mark N).

Lemma reduction_function :
 forall (M N P : lambda) (U : redexes),
 reduction M U N -> reduction M U P -> N = P.
Proof.
unfold reduction in |- *; intros; cut (comp (mark N) (mark P)).
intro; rewrite (inverse N); rewrite (inverse P); apply comp_unmark_eq;
 trivial.
apply mutual_residuals_comp with U (mark M) (mark M); trivial.
Qed.