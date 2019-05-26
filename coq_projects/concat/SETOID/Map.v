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
(*                                    Map.v                                 *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          General Algebra : Maps                                           *)
(*                                                                           *)
(*          Peter Aczel, Dec. 92                                             *)
(*          rev. Gerard Huet,  Aug. 1993                                     *)
(*                                                                           *)
(*****************************************************************************)

Require Export Setoid.

Set Implicit Arguments.
Unset Strict Implicit.

(* The set of maps between two Setoid *)

Section maps.

Variable A B : Setoid.

Definition Map_law (f : A -> B) := forall x y : A, x =_S y -> f x =_S f y.

Structure > Map : Type :=  {Ap :> A -> B; Pres :> Map_law Ap}.

(*** rewrite rule ***)

Lemma Pres1 : forall (m : Map) (x y : A), x =_S y -> m x =_S m y.
Proof.
exact Pres.
Qed.

(* *)

Definition Ext (f g : Map) := forall x : A, f x =_S g x.

Lemma Ext_equiv : Equivalence Ext.
Proof.
intros; apply Build_Equivalence.
unfold Reflexive in |- *; unfold Ext in |- *; intros f x.
apply Refl.
apply Build_Partial_equivalence.
unfold Transitive in |- *; unfold Ext in |- *; intros f g h e1 e2 x.
(* *) apply Trans with (g x).
apply (e1 x).
apply (e2 x).
unfold Symmetric in |- *; unfold Ext in |- *; intros f g e x.
apply Sym; trivial.
Qed.

Canonical Structure Map_setoid : Setoid := Ext_equiv.

End maps.

Infix "=_M" := Ext (at level 70).
Infix "==>" := Map_setoid (at level 95, right associativity).

(* Identity Map *)

Section id_map_def.

Variable A : Setoid.

Definition Id_fun (x : A) := x.
     
Lemma Id_fun_map_law : Map_law Id_fun.
Proof.
unfold Map_law in |- *; trivial.
Qed.

Canonical Structure Id_map : Map A A := Id_fun_map_law.
  
End id_map_def.
 

(* composition of two Maps *)

Section mcomp.

Variables (A B C : Setoid) (f : Map A B) (g : Map B C).

Definition Comp_fun (x : A) := g (f x).

Lemma Comp_fun_map_law : Map_law Comp_fun.
Proof.
unfold Map_law in |- *; intros a1 a2 H.
unfold Comp_fun in |- *; simpl in |- *.
apply Pres1.
apply Pres1; trivial.
Qed.

Canonical Structure Comp_map : Map A C := Comp_fun_map_law.

End mcomp.

Infix "o_M" := Comp_map (at level 20, right associativity). 