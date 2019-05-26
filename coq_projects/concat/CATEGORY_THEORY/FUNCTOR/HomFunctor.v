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
(*          Category Theory : Hom Functors                                   *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export SET.
Require Export Functor.
Require Export Dual.

Set Implicit Arguments.
Unset Strict Implicit.

(* 1. Hom-Functor : C(a,-) : C-->SET *)

Section funset.

Variables (C : Category) (a : C).

(* to each object b of C, we associate Hom(a,b), a object of SET *)

Definition FunSET_ob (b : C) := a --> b.

 Section funset_map_def.

 Variable b c : C.

  Section funset_mor_def.

  Variable f : b --> c.
 
  Definition FunSET_mor1 (g : a --> b) := g o f.

  Lemma FunSET_map_law1 : Map_law FunSET_mor1.
  Proof.
  unfold Map_law, FunSET_mor1 in |- *.
  intros g h H.
  apply Comp_r; assumption.
  Qed.

  Canonical Structure FunSET_mor : Map (FunSET_ob b) (FunSET_ob c) :=
    FunSET_map_law1.

  End funset_mor_def.

 Lemma FunSET_map_law : Map_law FunSET_mor.
 Proof.
 unfold Map_law in |- *; simpl in |- *.
 unfold Ext in |- *; simpl in |- *.
 unfold FunSET_mor1, FunSET_ob in |- *.
 intros f g H h.
 apply Comp_l; assumption.
 Qed.

 Canonical Structure FunSET_map := Build_Map FunSET_map_law.

 End funset_map_def.

Lemma Fun_comp_law : Fcomp_law FunSET_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *; simpl in |- *.
unfold FunSET_mor1, FunSET_ob in |- *.
intros b c d f g h.
apply Ass.
Qed.

Lemma Fun_id_law : Fid_law FunSET_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold Id_fun in |- *.
unfold FunSET_mor1, FunSET_ob in |- *.
intros b f; apply Idr1.
Qed.

Canonical Structure FunSET := Build_Functor Fun_comp_law Fun_id_law.

End funset.



