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
(*          Category Product : Projection Functors                           *)
(*                                                                           *)
(*          Amokrane Saibi,  May 1994                                        *)
(*                                                                           *)
(*****************************************************************************)

Require Export PROD.
Require Export Functor. 

Set Implicit Arguments.
Unset Strict Implicit.

(* Projection Functors *)

Section prod_proj.

Variable A B : Category.

(* Fst *)

Lemma Fst_map_law : forall a b : PROD A B, Map_law (Hom_l (u:=a) (t:=b)).
Proof.
unfold Map_law in |- *.
intros a b; unfold Equal at 1 in |- *; simpl in |- *.
unfold Equal_Pmor in |- *; intros f g H.
elim H; intros; assumption.
Qed.

Canonical Structure Fst_map (a b : PROD A B) :=
  Build_Map (Fst_map_law (a:=a) (b:=b)).

Lemma Fst_comp_law : Fcomp_law Fst_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros a b c f g.
apply Refl.
Qed.

Lemma Fst_id_law : Fid_law Fst_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro a; apply Refl.
Qed.
 
Canonical Structure Fst := Build_Functor Fst_comp_law Fst_id_law.

(* Snd *)

Lemma Snd_map_law : forall a b : PROD A B, Map_law (Hom_r (u:=a) (t:=b)).
Proof.
unfold Map_law in |- *.
intros a b; unfold Equal at 1 in |- *; simpl in |- *.
unfold Equal_Pmor in |- *; intros f g H.
elim H; intros; assumption.
Qed.

Canonical Structure Snd_map (a b : PROD A B) :=
  Build_Map (Snd_map_law (a:=a) (b:=b)).

Lemma Snd_comp_law : Fcomp_law Snd_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
intros a b c f g.
apply Refl.
Qed.

Lemma Snd_id_law : Fid_law Snd_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
intro a; apply Refl.
Qed.
 
Canonical Structure Snd := Build_Functor Snd_comp_law Snd_id_law.

End prod_proj.