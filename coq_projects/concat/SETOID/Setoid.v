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
(*                                 Setoid.v                                 *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          General Algebra : Setoids                                        *)
(*                                                                           *)
(*          Peter Aczel, Dec. 92                                             *)
(*          rev. Gerard Huet,  Aug. 1993                                     *)
(*                                                                           *)
(*****************************************************************************)

Require Export Relations.

Set Implicit Arguments.
Unset Strict Implicit.
Global Set Asymmetric Patterns.

Structure > Setoid : Type := 
  {Carrier :> Type; Equal : Relation Carrier; Prf_equiv :> Equivalence Equal}.

Infix "=_S" := Equal (at level 70).


(*** rewrite rules ***)

Lemma Refl : forall (S : Setoid) (x : S), x =_S x.
Proof.
intro S; exact (Prf_refl S).
Qed.

Lemma Sym : forall (S : Setoid) (x y : S), x =_S y -> y =_S x.
Proof.
intro S; exact (Prf_sym S).
Qed.

Lemma Trans : forall (S : Setoid) (x y z : S), x =_S y -> y =_S z -> x =_S z.
Proof.
intro S; exact (Prf_trans S).
Qed.

(* *)

(* An example *)

Inductive Nat : Type :=
  | Z : Nat
  | Suc : Nat -> Nat.

Definition Eq_Nat (N1 N2 : Nat) := N1 = N2.

Lemma Eq_Nat_equiv : Equivalence Eq_Nat.
Proof.
apply Build_Equivalence; unfold Eq_Nat in |- *.
auto.
apply Build_Partial_equivalence.
unfold Transitive in |- *; intros x y z H1 H2; apply (trans_eq H1 H2).
unfold Symmetric in |- *; intros x y H1; apply (sym_eq H1).
Qed.
 
Definition Set_of_nat : Setoid := Eq_Nat_equiv.

(* Alternative : PERS instead of Equivalences *)

Structure > PSetoid : Type := 
  {PCarrier :> Type;
   Coherence : Relation PCarrier;
   Prf_PER :> Partial_equivalence Coherence}.

Definition Total (A : PSetoid) (x : A) := Coherence x x.




