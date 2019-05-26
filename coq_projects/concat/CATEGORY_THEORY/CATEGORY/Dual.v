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
(*          Category Theory : Dual Category                                  *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

Section d_cat.

Variable C : Category.

Definition DHom (a b : C) := b --> a.

(* construire un Comp_Type *)

Definition Comp_Darrow (a b c : C) (df : DHom a b) (dg : DHom b c) := dg o df.
                          
Lemma Comp_dual_congl : Congl_law Comp_Darrow.
Proof.
unfold Congl_law in |- *; simpl in |- *.
unfold Comp_Darrow in |- *; simpl in |- *.
intros a b c f g h eqf_g.
unfold DHom in |- *; apply Comp_r; apply eqf_g.
Qed.
                          
Lemma Comp_dual_congr : Congr_law Comp_Darrow.
Proof.
unfold Congr_law in |- *; simpl in |- *.
unfold Comp_Darrow in |- *; simpl in |- *.
intros a b c f g h eqf_g.
unfold DHom in |- *; apply Comp_l; apply eqf_g.
Qed.

Definition Comp_Dual := Build_Comp Comp_dual_congl Comp_dual_congr.
            
Lemma Assoc_Dual : Assoc_law Comp_Dual.
Proof.
unfold Assoc_law, DHom, Cat_comp, Ap2 in |- *; simpl in |- *. 
unfold Comp_Darrow in |- *.
intros a b c d df dg dh.
apply Ass1.
Qed.

Lemma Idl_Dual : Idl_law (Hom:=DHom) Comp_Dual (Id (c:=C)).
Proof.
unfold Idl_law, DHom, Cat_comp, Ap2 in |- *; simpl in |- *. 
unfold Comp_Darrow in |- *.
intros a b df.
apply Idr1.
Qed.

Lemma Idr_Dual : Idr_law (Hom:=DHom) Comp_Dual (Id (c:=C)).
Proof.
unfold Idr_law, DHom, Cat_comp, Ap2 in |- *; simpl in |- *. 
unfold Comp_Darrow in |- *.
intros a b df.
apply Idl1.
Qed.

Canonical Structure Dual := Build_Category Assoc_Dual Idl_Dual Idr_Dual.

End d_cat.
