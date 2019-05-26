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


(*****************************************************************************)
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          Category Theory : Natural Transformations                        *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export Functor.
Require Export Setoid_dup2.

Set Implicit Arguments.
Unset Strict Implicit.

(* Natural Transformations *)

Section nt_def.

Variables (C D : Category) (F G : Functor C D).

Definition NT_law (T : forall a : C, F a --> G a) :=
  forall (a b : C) (f : a --> b), FMor F f o T b =_S T a o FMor G f.

Structure > NT : Type := 
  {ApNT :> forall a : C, F a --> G a; Prf_NT_law :> NT_law ApNT}.

(*** rewrite rules ***)

Lemma NatCond :
 forall (T : NT) (a b : C) (f : a --> b), FMor F f o T b =_S T a o FMor G f.
Proof.
exact Prf_NT_law.
Qed.

Lemma NatCond1 :
 forall (T : NT) (a b : C) (f : a --> b), T a o FMor G f =_S FMor F f o T b.
Proof.
intros T a b f; apply Sym; apply (Prf_NT_law T f).
Qed.

(* *)

End nt_def.

(* Natural Transformations Setoid between F and G*)

Section setoid_nt.

Variables (C D : Category) (F G : Functor C D).

Definition Equal_NT (T T' : NT F G) := forall a : C, T a =_S T' a.

Lemma Equal_NT_equiv : Equivalence Equal_NT.
Proof.
apply Build_Equivalence; unfold Equal_NT in |- *.
unfold Reflexive in |- *; intros T a; apply Refl.
apply Build_Partial_equivalence.
unfold Transitive in |- *; intros T1 T2 T3 H H0 a.
(* *) apply Trans with (ApNT T2 a); auto.
unfold Symmetric in |- *; intros T1 T2 H a.
apply Sym; apply H.
Qed.

Canonical Structure NT_setoid : Setoid'' := Equal_NT_equiv.

End setoid_nt.

Infix "=_NT" := Equal_NT (at level 70).
