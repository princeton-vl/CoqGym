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
(*	                       Terminal Object in SET          		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export SET.
Require Export Single.
Require Export CatProperty.

Set Implicit Arguments.
Unset Strict Implicit.

(* le(s) setoid(s) singleton  est terminal *)
(* preuve que Single est terminal *)

Section set_terminal.

Variable S : Setoid.

Definition To_Single_fun (x : S) := Elt.
        
Lemma To_Single_map_law : Map_law To_Single_fun.
Proof.
unfold Map_law in |- *.
intros; exact I.
Qed.

Definition To_Single := Build_Map To_Single_map_law.

End set_terminal.

Lemma Single_is_Terminal : IsTerminal To_Single.
Proof.
red in |- *; intros a f; simpl in |- *; unfold Ext in |- *; intro x; exact I. 
Defined.

Definition SET_Terminal : Terminal SET := Single_is_Terminal.