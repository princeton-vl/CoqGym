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
(*          The Functor Category                                             *)
(*                                                                           *)
(*          Amokrane Saibi,  May 1994                                        *)
(*                                                                           *)
(*****************************************************************************)


Require Export Ntransformation.
Require Export Category_dup2.

Set Implicit Arguments.
Unset Strict Implicit.

(* Functor Category *)

Section cat_functor.

Variable C D : Category.

 Section compnt.

 Variables (F G H : Functor C D) (T : NT F G) (T' : NT G H).

 Definition Comp_tau (a : C) := T a o T' a.

 Lemma Comp_tau_nt_law : NT_law Comp_tau.
 Proof.
 unfold Comp_tau in |- *; unfold NT_law in |- *.
 intros a b f.
 (* F(f)o((tauFG b)o(tauGH b)) = ((tauFG a)o(tauGH a))oH(f) *)
 (* *) apply Trans with ((FMor F f o T b) o T' b).
 (* F(f)o((T b)o(T' b)) = (F(f)o(T b))o(T' b) *)
 apply Ass.
 (* (F(f)o(T' b))o(T' b) = ((T a)o(T' a))oH(f) *) 
 (* *) apply Trans with ((T a o FMor G f) o T' b).        
 (* (F(f)o(T' b))o(T' b) = ((T a)oG(f))o(T' b) *) 
 apply Comp_r; apply NatCond.
 (*  ((T a)oG(f))o(T' b) = ((T a)o(T' a))oH(f) *) 
 (* *) apply Trans with (T a o FMor G f o T' b).        
 (* ((T a)oG(f))o(T' b) = (T a)o(G(f)o(T' b)) *)
 apply Ass1.
 (* (T a)o(G(f)o(T' b)) = ((T a)o(T' a))oH(f) *) 
 (* *) apply Trans with (T a o T' a o FMor H f).
 (* (T a)o(G(f)o(T' b)) = (T a)o((T' a)oH(f)) *)
 (* G(f)o(T' b) = (T' a)oH(f) *)
 apply Comp_l; apply NatCond.
 (* (T a)o(G(f)o(T' b)) = ((T a)o(G(f))o(T' b) *)
 apply Ass.
 Qed.

 Canonical Structure CompV_NT : NT_setoid F H := Comp_tau_nt_law.

 End compnt.

Lemma CompV_NT_congl : Congl_law'' CompV_NT.  
Proof.
unfold Congl_law'' in |- *; simpl in |- *.
unfold Equal_NT, CompV_NT in |- *; simpl in |- *.
intros F G H T1 T2 T3 eqT1_T2 a; unfold Comp_tau in |- *.
apply Comp_l; apply eqT1_T2.
Qed.

Lemma CompV_NT_congr : Congr_law'' CompV_NT.  
Proof.
unfold Congr_law'' in |- *; simpl in |- *.
unfold Equal_NT, CompV_NT in |- *; simpl in |- *.
intros F G H T1 T2 T3 eqT1_T2 a; unfold Comp_tau in |- *.  
apply Comp_r; apply eqT1_T2.
Qed.

Definition Comp_CatFunct := Build_Comp'' CompV_NT_congl CompV_NT_congr.
   
Lemma Assoc_CatFunct : Assoc_law'' Comp_CatFunct.
Proof.
unfold Assoc_law'' in |- *; intros a b c f.
intros T1 T2 T3.
unfold Cat_comp'', Ap2'' in |- *; simpl in |- *.
unfold Equal_NT, CompV_NT in |- *; simpl in |- *.
intro x; unfold Comp_tau in |- *; simpl in |- *.
apply Ass.
Qed.

(* Id *)

 Section id_catfunct_def.

 Variable F : Functor C D.

 Definition Id_CatFunct_tau (a : C) := Id (F a).
 
 Lemma Id_CatFunct_nt_law : NT_law Id_CatFunct_tau.
 Proof.
 unfold NT_law, Id_CatFunct_tau in |- *; intros a b f. 
 (* *) apply Trans with (FMor F f).
 apply Idr1.
 apply Idl1.
 Qed.
  
 Canonical Structure Id_CatFunct := Build_NT Id_CatFunct_nt_law.

 End id_catfunct_def.

Lemma Idl_CatFunct : Idl_law'' Comp_CatFunct Id_CatFunct.
Proof.
red in |- *; simple induction f.
unfold Comp_CatFunct in |- *; unfold Id_CatFunct in |- *; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *.
unfold Comp_tau in |- *; simpl in |- *.
unfold Id_CatFunct_tau in |- *; intros.
apply Idl.
Qed.

Lemma Idr_CatFunct : Idr_law'' Comp_CatFunct Id_CatFunct.
Proof.
red in |- *; simple induction f.
unfold Comp_CatFunct in |- *; unfold Id_CatFunct in |- *; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *.
unfold Comp_tau in |- *; simpl in |- *.
unfold Id_CatFunct_tau in |- *; intros.
apply Idr.
Qed.

Canonical Structure FUNCT :=
  Build_Category'' Assoc_CatFunct Idl_CatFunct Idr_CatFunct.

End cat_functor.

Infix "o_NTv" := CompV_NT (at level 20, right associativity).

