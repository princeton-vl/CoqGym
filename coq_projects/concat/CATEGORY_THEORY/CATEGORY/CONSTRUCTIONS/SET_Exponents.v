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
(*	                   Exponents in SET              		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export SET_BinProds.
Require Export Exponents.

Set Implicit Arguments.
Unset Strict Implicit.

(* expo dans SET *)

Section verif_expo.

Variable A B : Setoid.

(* B(expo A) = A==>B *)

Definition S_expo := Map A B.

(* de'finition de eval *)

Definition S_eval_fun (fxa : SPROD (A ==> B) A) := Sprod_l fxa (Sprod_r fxa).

Lemma S_eval_map_law : Map_law S_eval_fun.
Proof.
unfold Map_law in |- *.
intros fxa gxa'; elim fxa; intros f a; elim gxa'; intros g a'; simpl in |- *.
unfold S_eval_fun in |- *; simpl in |- *.
unfold Equal_Sprod in |- *; simpl in |- *.
intro H; elim H; intros H1 H2.
(* *) apply Trans with (f a').
apply Pres1; trivial.
apply (H1 a').
Qed.

Definition S_eval := Build_Map S_eval_map_law.

(* de'finition de lambda *)

 Section set_lambda_def.

 Variable C : Setoid.

  Section set_lambda_fun_def.

  Variable f : Map (SPROD C A) B.

   Section set_lambda_fun1_def.

   Variable c : C.

   Definition S_lambda_fun2 (a : A) := f (Build_Sprod c a).

   Lemma S_lambda_map_law2 : Map_law S_lambda_fun2.
   Proof.
   unfold Map_law in |- *.
   intros a1 a2 H; unfold S_lambda_fun2 in |- *.                         
   apply Pres1.
   simpl in |- *; unfold Equal_Sprod in |- *; simpl in |- *; split.
   apply Refl.
   trivial.
   Qed.

   Definition S_lambda_fun1 := Build_Map S_lambda_map_law2.

   End set_lambda_fun1_def.

  Lemma S_lambda_map_law1 : Map_law S_lambda_fun1.
  Proof.
  unfold Map_law in |- *.
  intros c1 c2 H; unfold S_lambda_fun1 in |- *; simpl in |- *.
  unfold Ext in |- *; intro a; unfold S_lambda_fun2 in |- *; simpl in |- *.
  apply Pres1.
  simpl in |- *; unfold Equal_Sprod in |- *; simpl in |- *; split.
  trivial.
  apply Refl.
  Qed.

  Definition S_lambda1_fun := Build_Map S_lambda_map_law1.

  End set_lambda_fun_def.

 Lemma S_lambda_map_law : Map_law S_lambda1_fun.
 Proof.
 unfold Map_law in |- *.
 intros f g H; unfold S_lambda1_fun in |- *; simpl in |- *.
 unfold Ext in |- *; simpl in |- *; intros c.
 unfold Ext in |- *; simpl in |- *; intro a. 
 unfold S_lambda_fun2 in |- *.
 apply (H (Build_Sprod c a)).
 Qed.

 Definition S_Lambda := Build_Map S_lambda_map_law.

 End set_lambda_def. 

(* ve'rification des lois *)

Lemma S_beta_rule : Beta_rule_law (C1:=SET_hasBinProd) S_eval S_Lambda.
Proof.
unfold Beta_rule_law in |- *; simpl in |- *.
intros C f; unfold Ext in |- *; simpl in |- *.
intro cxa; unfold S_eval_fun in |- *; simpl in |- *.
unfold S_lambda_fun2 in |- *.
apply Pres1.
simpl in |- *; unfold Equal_Sprod in |- *; simpl in |- *; split.
apply Refl.
unfold Id_fun in |- *; apply Refl.
Qed.
                    
Lemma S_eta_rule : Eta_rule_law (C1:=SET_hasBinProd) S_eval S_Lambda.
Proof.
unfold Eta_rule_law in |- *; simpl in |- *.
intros C h; unfold Ext in |- *; simpl in |- *.
intro c; unfold Ext in |- *; simpl in |- *.
intro a; unfold S_eval_fun in |- *; simpl in |- *. 
unfold Comp_fun in |- *; simpl in |- *.
apply Pres1.
apply Refl.
Qed.

Canonical Structure SET_hasExponent := Build_Exponent S_beta_rule S_eta_rule.

End verif_expo.
