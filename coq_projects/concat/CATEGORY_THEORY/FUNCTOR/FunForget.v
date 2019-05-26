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
(*	               Forgetful Functor : MON -> SET                        *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export MON.
Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* Foncteur d'oubli *)

Section forget_map_def.

Variable m1 m2 : Monoid.

Lemma FunForget_map_law : Map_law (MonMap (m1:=m1) (m2:=m2)).
Proof.
unfold Map_law in |- *; simpl in |- *.
unfold Equal_MonMor in |- *; trivial.
Qed.

Canonical Structure FunForget_map := Build_Map FunForget_map_law.

End forget_map_def.

Lemma FunForget_fcomp_law : Fcomp_law FunForget_map.
Proof.
unfold Fcomp_law in |- *; simpl in |- *.
unfold Comp_MonMor_map, Ext in |- *.
intros m1 m2 m3 f g x; apply Refl.
Qed.

Lemma FunForget_fid_law : Fid_law FunForget_map.
Proof.
unfold Fid_law in |- *; simpl in |- *.
unfold Id_MON_map, Ext in |- *.
intros m x; apply Refl.
Qed.

Canonical Structure FunForget :=
  Build_Functor FunForget_fcomp_law FunForget_fid_law.