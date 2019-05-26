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
(*                                    CAT.v                                 *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Coq - Calculus of Inductive Constructions V5.10           *)
(*****************************************************************************)
(*                                                                           *)
(*          Category Theory : The Category CAT                               *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)


Require Export IdCAT.
Require Export Category_dup1.

Set Implicit Arguments.
Unset Strict Implicit.

(* Functor composition operator *)

Lemma Comp_Functor_congl : Congl_law' Comp_Functor.
Proof.
unfold Congl_law' in |- *; simpl in |- *.
unfold Equal_Functor, Comp_Functor in |- *.
intros A B C F G H eq_FG a1 a2 f.
unfold FMor in |- *; simpl in |- *.
unfold Comp_FOb, Comp_FMor in |- *.
apply eq_FG.
Qed.

Lemma Comp_Functor_congr : Congr_law' Comp_Functor.
Proof.
unfold Congr_law' in |- *; simpl in |- *.
unfold Equal_Functor, Comp_Functor in |- *.
intros A B C F G H eq_FG a1 a2 f.
unfold FMor in |- *; simpl in |- *.
unfold Comp_FOb, Comp_FMor in |- *.
elim (eq_FG a1 a2 f); intros g eq_Ff_g.
apply Build_Equal_hom; apply FPres; assumption.
Qed.

Definition Comp_CAT := Build_Comp' Comp_Functor_congl Comp_Functor_congr.
     
Lemma Assoc_CAT : Assoc_law' Comp_CAT.
Proof.
unfold Assoc_law', Cat_comp' in |- *; simpl in |- *.
intros C D E F G H X.
unfold Equal_Functor in |- *; simpl in |- *.
unfold Ap2 in |- *; simpl in |- *; auto.
Qed.

(* Id *)

Lemma Idl_CAT : Idl_law' Comp_CAT Id_CAT.
Proof.
unfold Idl_law', Cat_comp', Ap2 in |- *; simpl in |- *.
intros C D G; unfold Comp_Functor, Equal_Functor in |- *.
intros a b f; unfold FMor in |- *; simpl in |- *.
unfold Comp_FMor in |- *; unfold Id_CAT, FMor in |- *; simpl in |- *.
auto.
Qed.

Lemma Idr_CAT : Idr_law' Comp_CAT Id_CAT.
Proof.
unfold Idr_law', Cat_comp', Ap2 in |- *; simpl in |- *.
intros C D G; unfold Comp_Functor, Equal_Functor in |- *.
intros a b f; unfold FMor in |- *; simpl in |- *.
unfold Comp_FMor in |- *; unfold Id_CAT, FMor in |- *; simpl in |- *.
auto.
Qed.

Canonical Structure CAT : Category' :=
  Build_Category' Assoc_CAT Idl_CAT Idr_CAT.
              