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
(*                               Noetherian.v                               *)
(****************************************************************************)

Require Import Relations.

Set Implicit Arguments.
Unset Strict Implicit.

Section Noether.
   Variable U : Type.
   Variable R : Relation U.
   
   Inductive noetherian : U -> Prop :=
       Build_noetherian :
         forall x : U, (forall y : U, R x y -> noetherian y) -> noetherian x.
   
   Definition Noetherian : Prop := forall x : U, noetherian x.
   
End Noether.

Hint Resolve Build_noetherian.

Theorem Noetherian_contains_Noetherian :
 forall (U : Type) (R R' : Relation U),
 Noetherian R -> Contains R R' -> Noetherian R'.
Proof.
unfold Noetherian at 2 in |- *.
intros U R R' H' H'0 x.
elim H' with x; auto.
Qed.




(* $Id$ *)