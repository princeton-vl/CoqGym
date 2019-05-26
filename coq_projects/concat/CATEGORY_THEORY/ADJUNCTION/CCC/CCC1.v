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
(*	            Adjunction Example : CCC                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Cartesian1.
Require Export CCC.
Require Export FunProd.

Set Implicit Arguments.
Unset Strict Implicit.

(* construire l'expo... a` partir d'un CCC *)

Section funprod_hasexpo.

Variable C : Category.
Variable H : HasBinProd C.

Definition HasExponent1 := forall a : C, RightAdj (Fun_prod H a).

Variable H1 : HasExponent1.

 Section funprod_expo.

 Variable a b : C.

 Let ua' := CoUnit (H1 a) b.

 Definition Expo1 := CoUA_ob ua'.

 Definition Eval1 := CoUA_mor ua'.

  Section lambda1_def.

  Variable c : C.

  Definition Lambda1_mor (f : H_obj_prod H c a --> b) := CoUA_diese ua' f.

  Lemma Lambda1_map_law : Map_law Lambda1_mor.
  Proof.
  unfold Map_law in |- *; intros f g H'.
  unfold Lambda1_mor in |- *.
  apply (Codiese_map ua' (x:=f) (y:=g)).
  trivial.
  Qed.

  Canonical Structure Lambda1 := Build_Map Lambda1_map_law.

  End lambda1_def.

 Lemma Prf_beta_rule1 : Beta_rule_law Eval1 Lambda1.
 Proof.
 unfold Beta_rule_law in |- *; intros c f.
 unfold Lambda1, Eval1 in |- *.
 apply (Prf_isCoUA_law1 ua' f).
 Qed.

 Lemma Prf_eta_rule1 : Eta_rule_law Eval1 Lambda1.
 Proof.
 unfold Eta_rule_law in |- *; intros c h; simpl in |- *.
 unfold Lambda1_mor in |- *.
 apply Sym.
 apply (Prf_isCoUA_law2 ua' (a':=c) (f:=Mor_prod H h (Id a) o Eval1) (g:=h)).
 unfold CoUA_eq in |- *.
 apply Refl.
 Qed.

 End funprod_expo.

 Definition HasExp1_to_HasExp : HasExponent H :=
   fun a b : C =>
   Build_Exponent (Prf_beta_rule1 (a:=a) (b:=b))
     (Prf_eta_rule1 (a:=a) (b:=b)).

End funprod_hasexpo.

Coercion HasExp1_to_HasExp : HasExponent1 >-> HasExponent.

Structure IsCCC1 (C : Category) : Type := 
  {CCC1_Car :> IsCartesian1 C; CCC1_exponent :> HasExponent1 CCC1_Car}.

Coercion CCC1_to_CCC (C : Category) (H : IsCCC1 C) :=
  Build_IsCCC (CCC_isCar:=H) H.
