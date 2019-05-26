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
(*  Category Theory : Natural Transformations between Hom-Functors           *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export HomFunctor.
Require Export Ntransformation.

Set Implicit Arguments.
Unset Strict Implicit.

(* Natural transformation Y(f):C(b,-)-->C(a,-), with f:a-->b in C *)

Section funset_nt.

Variables (C : Category) (b a : C) (f : a --> b).

Section nth_map_def.

 Variable c : C.

 Definition NtH_arrow (h : b --> c) := f o h.

 Lemma NtH_map_law : Map_law NtH_arrow.
 Proof.
 unfold Map_law, NtH_arrow in |- *; intros.
 apply Comp_l; assumption.
 Qed.

 Definition NtH_map : Map (FunSET b c) (FunSET a c) := NtH_map_law.

End nth_map_def.

Lemma NtH_nt_law : NT_law NtH_map.
Proof.
unfold NT_law in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold Comp_fun in |- *; simpl in |- *.
unfold NtH_arrow, FunSET_mor1, FunSET_ob in |- *.
intros; apply Ass.
Qed.

Canonical Structure NtH := Build_NT NtH_nt_law.

End funset_nt.

