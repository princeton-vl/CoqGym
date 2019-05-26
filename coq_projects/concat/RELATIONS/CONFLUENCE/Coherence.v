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
(*                               Coherence.v                                *)
(****************************************************************************)

Hint Resolve refl_equal. (* TO BE REMOVED *)
Require Import Relations.
Require Import Confluence.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem Rstar_reflexive :
 forall (U : Type) (R : Relation U), Reflexive (Rstar R).
Proof.
auto.
Qed.

Theorem Rplus_contains_R :
 forall (U : Type) (R : Relation U), Contains (Rplus R) R.
Proof.
auto.
Qed.

Theorem Rstar_contains_R :
 forall (U : Type) (R : Relation U), Contains (Rstar R) R.
Proof.
intros U R; red in |- *; intros x y H'; apply Rstar_n with y; auto.
Qed.

Theorem Rstar_contains_Rplus :
 forall (U : Type) (R : Relation U), Contains (Rstar R) (Rplus R).
Proof.
intros U R; red in |- *.
intros x y H'; elim H'.
generalize Rstar_contains_R; intro T; red in T; auto.
intros x0 y0 z H'0 H'1 H'2; apply Rstar_n with y0; auto.
Qed.

Theorem Rstar_transitive :
 forall (U : Type) (R : Relation U), Transitive (Rstar R).
Proof.
intros U R; red in |- *.
intros x y z H'; elim H'; auto.
intros x0 y0 z0 H'0 H'1 H'2 H'3; apply Rstar_n with y0; auto.
Qed.

Theorem Rstar_cases :
 forall (U : Type) (R : Relation U) (x y : U),
 Rstar R x y -> x = y \/ (exists u : U, R x u /\ Rstar R u y).
Proof.
intros U R x y H'; elim H'; auto.
intros x0 y0 z H'0 H'1 H'2; right; exists y0; auto.
Qed.

Theorem Rstar_equiv_Rstar1 :
 forall (U : Type) (R : Relation U), Same_relation (Rstar R) (Rstar1 R).
Proof.
generalize Rstar_contains_R; intro T; red in T.
intros U R; unfold Same_relation, Contains in |- *.
split; intros x y H'; elim H'; auto.
generalize Rstar_transitive; intro T1; red in T1.
intros x0 y0 z H'0 H'1 H'2 H'3; apply T1 with y0; auto.
intros x0 y0 z H'0 H'1 H'2; apply Rstar1_n with y0; auto.
Qed.

Theorem Rsym_imp_Rstarsym :
 forall (U : Type) (R : Relation U), Symmetric R -> Symmetric (Rstar R).
Proof.
intros U R H'; red in |- *.
intros x y H'0; elim H'0; auto.
intros x0 y0 z H'1 H'2 H'3.
generalize Rstar_transitive; intro T; red in T.
apply T with y0; auto.
apply Rstar_n with x0; auto.
Qed.

Theorem Sstar_contains_Rstar :
 forall (U : Type) (R S : Relation U),
 Contains (Rstar S) R -> Contains (Rstar S) (Rstar R).
Proof.
unfold Contains in |- *.
intros U R S H' x y H'0; elim H'0; auto.
generalize Rstar_transitive; intro T; red in T.
intros x0 y0 z H'1 H'2 H'3; apply T with y0; auto.
Qed.

Theorem star_monotone :
 forall (U : Type) (R S : Relation U),
 Contains S R -> Contains (Rstar S) (Rstar R).
Proof.
intros U R S H'.
apply Sstar_contains_Rstar.
generalize (Rstar_contains_R (R:=S)); auto.
Qed.

Theorem RstarRplus_RRstar :
 forall (U : Type) (R : Relation U) (x y z : U),
 Rstar R x y -> Rplus R y z -> exists u : U, R x u /\ Rstar R u z.
Proof.
generalize Rstar_contains_Rplus; intro T; red in T.
generalize Rstar_transitive; intro T1; red in T1.
intros U R x y z H'; elim H'.
intros x0 H'0; elim H'0.
intros; exists y0; auto.
intros; exists y0; auto.
intros; exists y0; auto.
split; [ try assumption | idtac ].
apply T1 with z0; auto.
Qed.

Theorem Rstar_imp_coherent :
 forall (U : Type) (R : Relation U) (x y : U), Rstar R x y -> coherent R x y.
Proof.
intros U R x y H'; red in |- *.
exists y; auto.
Qed.
Hint Resolve Rstar_imp_coherent.

Theorem coherent_symmetric :
 forall (U : Type) (R : Relation U), Symmetric (coherent R).
Proof.
unfold coherent at 1 in |- *.
intros U R; red in |- *.
intros x y h; elim h; intros z h0; elim h0; intros H' H'0; clear h h0.
exists z; auto.
Qed.

(* $Id$ *)