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
(*	                The Unit Setoid {*}              		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Setoid.
Require Export BasicTypes.

Set Implicit Arguments.
Unset Strict Implicit.

(* setoid a` un elet *)

Definition Equal_Single (a b : UnitType) := True.

Lemma Equal_Single_equiv : Equivalence Equal_Single.
Proof.
unfold Equal_Single in |- *; apply Build_Equivalence;
 [ trivial | apply Build_Partial_equivalence ]; red in |- *; 
 trivial.
Qed.

Canonical Structure Single : Setoid := Equal_Single_equiv.

Hint Resolve Elt.


