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
(*									     *)
(*	                       Setoid Product               		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Map.

Set Implicit Arguments.
Unset Strict Implicit.

(* Produit de deux Setoid *)

Section s_prod.

Variable A B : Setoid.

Structure Sprod : Type :=  {Sprod_l : A; Sprod_r : B}.

Definition Equal_Sprod (a1xb1 a2xb2 : Sprod) :=
  Sprod_l a1xb1 =_S Sprod_l a2xb2 /\ Sprod_r a1xb1 =_S Sprod_r a2xb2.

Lemma Equal_Sprod_equiv : Equivalence Equal_Sprod.
Proof.
apply Build_Equivalence.
unfold Reflexive in |- *; simple induction x; intros a b;
 unfold Equal_Sprod in |- *; simpl in |- *.
split.
apply Refl.
apply Refl.
apply Build_Partial_equivalence.
unfold Transitive in |- *.
simple induction x; intros a b; simple induction y; intros a' b';
 simple induction z; intros a'' b''.
unfold Equal_Sprod in |- *; simpl in |- *.
intros H H0; elim H; intros H1 H2; elim H0; intros H3 H4.
split.
apply Trans with a'; trivial.
apply Trans with b'; trivial.
unfold Symmetric in |- *; simple induction x; intros a b; simple induction y;
 intros a' b'.
unfold Equal_Sprod in |- *; simpl in |- *.
intros H; elim H; intros H1 H2.
split.
apply Sym; trivial.
apply Sym; trivial.
Qed.

Canonical Structure SPROD : Setoid := Equal_Sprod_equiv.

(* AxB = (S_PROD A B) *) 
(* Sprod_l et Sprod_r sont en fait des Map *)

Lemma Proj1_SPROD_map_law : Map_law (Sprod_l:SPROD -> A).
Proof.
unfold Map_law in |- *; simpl in |- *.
simple induction x; intros a b; simple induction y; intros a' b'.
simpl in |- *; unfold Equal_Sprod in |- *; simpl in |- *.
simple induction 1; trivial.
Qed.

Canonical Structure Proj1_SPROD : Map SPROD A := Proj1_SPROD_map_law.

Lemma Proj2_SPROD_map_law : Map_law (Sprod_r:SPROD -> B).
Proof.
unfold Map_law in |- *; simpl in |- *.
simple induction x; intros a b; simple induction y; intros a' b'.
simpl in |- *; unfold Equal_Sprod in |- *; simpl in |- *.
simple induction 1; trivial.
Qed.

Canonical Structure Proj2_SPROD : Map SPROD B := Proj2_SPROD_map_law.

End s_prod.
