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
(*	                   Natural Isomorphism            		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)
  

Require Export CatProperty.
Require Export CatFunct.

Set Implicit Arguments.
Unset Strict Implicit.

(* 1ere solution: def primitive *)

Section natiso_def.

Variable A B : Category.

Definition RNatIso_law (F G : Functor A B) (T : NT F G) 
  (T1 : NT G F) := T1 o_NTv T =_NT Id_CatFunct G.

Variable F G : Functor A B.

Definition AreNatIsos (T : NT F G) (T1 : NT G F) :=
  RNatIso_law T T1 /\ RNatIso_law T1 T.

Structure > NatIso : Type := 
  {NatIso_mor :> NT F G;
   NatIso_inv : NT G F;
   Prf_NatIso :> AreNatIsos NatIso_mor NatIso_inv}.

Lemma Idl_nat_inv :
 forall i : NatIso, RNatIso_law (NatIso_mor i) (NatIso_inv i).
Proof.
simple induction i; unfold AreNatIsos in |- *; intros T1 T2 p; elim p; auto.
Qed.

Lemma Idr_nat_inv :
 forall i : NatIso, RNatIso_law (NatIso_inv i) (NatIso_mor i).
Proof.
simple induction i; unfold AreNatIsos in |- *; intros T1 T2 p; elim p; auto.
Qed.

End natiso_def.


Section about_isIso.

Variables (A B : Category) (F G : Functor A B) (T : NT F G).

(* qq a. Ta isIso => T isIso *)

Variable h : forall a : A, G a --> F a.

Hypothesis H : forall a : A, AreIsos (T a) (h a).
   
Lemma NTinv_nt_law : NT_law h.
Proof.
unfold NT_law in |- *; intros a b f.
(* *) apply Trans with ((h a o T a o FMor G f) o h b).
apply Comp_r.
(* *) apply Trans with ((h a o T a) o FMor G f).
(* *) apply Trans with (Id (G a) o FMor G f).
apply Idl1.
apply Comp_r; apply Sym; apply (Idl_inv (H a)).
apply Ass1.
(* *) apply Trans with ((h a o FMor F f o T b) o h b).
apply Comp_r; apply Comp_l; apply NatCond1.
(* *) apply Trans with (h a o (FMor F f o T b) o h b).
apply Ass1.
apply Comp_l.
(* *) apply Trans with (FMor F f o T b o h b).
apply Ass1.
(* *) apply Trans with (FMor F f o Id _).
apply Comp_l; apply (Idr_inv (H b)).
apply Idr1.
Qed.

Canonical Structure NTinv := Build_NT NTinv_nt_law.

Lemma NT_areIso : AreNatIsos T NTinv.
Proof.
red in |- *; split; unfold RNatIso_law in |- *; unfold Equal_NT in |- *;
 simpl in |- *; unfold Comp_tau in |- *; simpl in |- *;
 unfold Id_CatFunct_tau in |- *; intro a.
apply (Idl_inv (H a)).
apply (Idr_inv (H a)).
Qed.

Canonical Structure NT_Iso : NatIso F G := NT_areIso.

(* T isIso => qq a. Ta isIso *)

Variable T1 : NT G F.

Hypothesis H' : AreNatIsos T T1.

Variable a : A.

Lemma NTa_areIso : AreIsos (T a) (T1 a).
Proof.
red in |- *; split; unfold RIso_law in |- *.
apply (Idl_nat_inv H' a).
apply (Idr_nat_inv H' a).
Qed.

Canonical Structure NTa_Iso : Iso (F a) (G a) := NTa_areIso.

End about_isIso.


