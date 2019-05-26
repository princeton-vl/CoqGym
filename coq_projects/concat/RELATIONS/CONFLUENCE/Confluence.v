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
(*                               Confluence.v                               *)
(****************************************************************************)

Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Confluence.
   Variable U : Type.
   Variable R : Relation U.
   
   Inductive Rstar : Relation U :=
     | Rstar_0 : forall x : U, Rstar x x
     | Rstar_n : forall x y z : U, R x y -> Rstar y z -> Rstar x z.
   
   Inductive Rstar1 : Relation U :=
     | Rstar1_0 : forall x : U, Rstar1 x x
     | Rstar1_1 : forall x y : U, R x y -> Rstar1 x y
     | Rstar1_n : forall x y z : U, Rstar1 x y -> Rstar1 y z -> Rstar1 x z.
   
   Inductive Rplus : Relation U :=
     | Rplus_0 : forall x y : U, R x y -> Rplus x y
     | Rplus_n : forall x y z : U, R x y -> Rplus y z -> Rplus x z.
   
   Definition Strongly_confluent : Prop :=
     forall x a b : U, R x a -> R x b -> exists z : U, R a z /\ R b z.

   Definition coherent (x y : U) : Prop :=
     exists z : U, Rstar x z /\ Rstar y z.
   
   Definition locally_confluent (x : U) : Prop :=
     forall y z : U, R x y -> R x z -> coherent y z.
   
   Definition Locally_confluent : Prop := forall x : U, locally_confluent x.
   
   Definition confluent (x : U) : Prop :=
     forall y z : U, Rstar x y -> Rstar x z -> coherent y z.
   
   Definition Confluent : Prop := forall x : U, confluent x.
   
End Confluence.
   
Hint Resolve Rstar_0.
Hint Resolve Rstar1_0.
Hint Resolve Rstar1_1.
Hint Resolve Rplus_0.



(* $Id$ *)