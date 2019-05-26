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
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*									     *)
(*	           Definition of Terminal by Adjunctions       		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export FunOne.
Require Export Adj_UA.

Set Implicit Arguments.
Unset Strict Implicit.

(* !C a un RAdj => C a un obj terminal *)

Section terminal1_def.

Variable C : Category.

SubClass Terminal1 := RightAdj (FunOne C).

Variable t : Terminal1.

Let ua' := CoUnit t Obone.

Definition Terminal1_ob := CoUA_ob ua'. 

Definition MorT1 (a : C) := CoUA_diese ua' (a':=a) Id_Obone.

Lemma Prf_isTerminal1 : IsTerminal MorT1.
Proof.
red in |- *; intros a f.
apply (Prf_isCoUA_law2 ua' (f:=Id_Obone) (g:=f)).
unfold CoUA_eq in |- *; exact I.
Qed.

Canonical Structure Terminal1_to_Terminal := Build_Terminal Prf_isTerminal1.

End terminal1_def.

Coercion Terminal1_to_Terminal : Terminal1 >-> Terminal.
