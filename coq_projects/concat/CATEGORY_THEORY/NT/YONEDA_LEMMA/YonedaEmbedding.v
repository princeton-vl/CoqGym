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
(*          Category Theory : Yoneda's Functor                               *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)


Require Export HomFunctor_NT.
Require Export CatFunct.
Require Export Functor_dup1.


Set Implicit Arguments.
Unset Strict Implicit.

(* Fonctor Y:C^o-->[C==>SET] *)

Section yoneda_functor.

Variable C : Category.

 Section funy_map_def.

 Variable a b : C.

 Lemma FunY_map_law : Map_law0'' (NtH (C:=C) (b:=a) (a:=b)).
 Proof.
 unfold Map_law0'', NtH in |- *; simpl in |- *.
 unfold Equal_NT in |- *; simpl in |- *.
 unfold Ext in |- *; simpl in |- *.
 unfold NtH_arrow in |- *; simpl in |- *.
 unfold FunSET_ob in |- *; intros.
 apply Comp_r; assumption.
 Qed.

 Canonical Structure FunY_map := Build_Map0'' FunY_map_law.

 End funy_map_def.

Lemma FunY_comp_law : Fcomp_law0'' (C:=Dual C) FunY_map.
Proof.
unfold Fcomp_law0'' in |- *; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold NtH_arrow in |- *; simpl in |- *.
unfold FunSET_ob, DHom in |- *.
intros a b c f g d h; apply Sym.
exact (Prf_ass g f h).
Qed.

Lemma FunY_id_law : Fid_law0'' (C:=Dual C) FunY_map.
Proof.
unfold Fid_law0'' in |- *; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *. 
unfold Ext in |- *; simpl in |- *.
unfold NtH_arrow in |- *; simpl in |- *.
unfold FunSET_ob in |- *.
unfold Id_fun in |- *; simpl in |- *.
intros a b f; unfold Comp in |- *; apply (Prf_idl (c:=C)).
Qed.

Canonical Structure FunY := Build_Functor0'' FunY_comp_law FunY_id_law.      

(* lemma : Y is full *)

Lemma Y_full :
 let f := fun (a b : C) (h : NT (FunSET a) (FunSET b)) => h a (Id a) in
 Full_law0'' (F:=FunY) f.
Proof.
unfold Full_law0'' in |- *; simpl in |- *; intros a b h.
unfold Equal_NT in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *.
unfold NtH_arrow in |- *.
unfold FunSET_ob in |- *.
intros c f; simpl in |- *.
(* *) apply Trans with (h c (Id a o f)).
apply Pres1.
apply Sym; unfold Comp in |- *; simpl in |- *; unfold FunSET_ob in |- *;
 apply (Prf_idl (c:=C)).
apply (Prf_NT_law h f (Id a)).
Qed.

(* Y is faithful *)

Lemma Y_faithful : Faithful_law0'' FunY.
Proof.
unfold Faithful_law0'' in |- *; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *.
unfold Ext in |- *; simpl in |- *; unfold DHom in |- *.
unfold NtH_arrow in |- *.
unfold FunSET_ob in |- *.
intros a b f g H.
(* *) apply Trans with (g o Id a).
(* *) apply Trans with (f o Id a).
apply Idr.
apply H.
apply Idr1.
Qed.

End yoneda_functor.


