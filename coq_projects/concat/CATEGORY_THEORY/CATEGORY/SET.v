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
(*          SET : The Category of Setoids                                    *)
(*                                                                           *)
(*          Peter Aczel, Dec. 92                                             *)
(*          rev. Gerard Huet,  Aug. 1993                                     *)
(*          rev. Amokrane Saibi,  May 1994                                   *)
(*                                                                           *)
(*****************************************************************************)

Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

(* Map composition operator *)

Lemma Comp_map_congl : Congl_law Comp_map.
Proof.
unfold Congl_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *; auto.
Qed.

Lemma Comp_map_congr : Congr_law Comp_map.
Proof.
unfold Congr_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *.
intros a b c f g h e x.
apply Pres1; auto.
Qed.

Definition Comp_SET := Build_Comp Comp_map_congl Comp_map_congr.

Lemma Assoc_SET : Assoc_law Comp_SET.
Proof.
unfold Assoc_law in |- *; simpl in |- *; intros.
unfold Ext in |- *; intro x; simpl in |- *.
apply Refl.
Qed.

(* Id *)

Definition Id_SET := Id_map.
 
Lemma Idl_SET : Idl_law Comp_SET Id_SET.
Proof.
unfold Idl_law in |- *; intros.
unfold Comp in |- *.
unfold Ap2 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intro x; apply Refl.
Qed.

Lemma Idr_SET : Idr_law Comp_SET Id_SET.
Proof.
unfold Idr_law in |- *; intros.
unfold Comp in |- *.
unfold Ap2 in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
intro x; apply Refl.
Qed.

Canonical Structure SET := Build_Category Assoc_SET Idl_SET Idr_SET.
