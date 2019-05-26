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
(*  Free Monoid functor is the Left adjoint of the Forgetful functor         *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export FunFreeMon.
Require Export FunForget_UA.
Require Export Th_Adjoint. 

Set Implicit Arguments.
Unset Strict Implicit.

Definition LeftAdj_FunForget := LeftAdjUA UA_FM.

Lemma Adj_FunFreeMon_FunForget : FunFreeMon =_F Adjoint LeftAdj_FunForget.
Proof.
unfold Equal_Functor in |- *; intros A B f.
apply Build_Equal_hom; simpl in |- *.
unfold Equal_MonMor in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; intro l.
elim l; simpl in |- *.
trivial.
intros c t H; split.
apply Refl.
trivial.
Qed.