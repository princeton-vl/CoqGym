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
(*          Category Theory : Dual Functor                                   *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export Dual.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

Section dfunctor_def.

Variables (A B : Category) (F : Functor A B).

Definition DFunctor_ob : Dual A -> Dual B := fun a : A => F a.

Definition DFunctor_map (b a : A) := FMap F a b.

Lemma DFunctor_comp_law : Fcomp_law (FOb:=DFunctor_ob) DFunctor_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros a b c f g.
exact (Prf_Fcomp_law F g f).  
Qed.

Lemma DFunctor_id_law : Fid_law (FOb:=DFunctor_ob) DFunctor_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro a; exact (Prf_Fid_law F a).     
Qed.

Canonical Structure Dfunctor :=
  Build_Functor DFunctor_comp_law DFunctor_id_law.

End dfunctor_def.






