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
(*	                Category with Exponents                              *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Binary_Products.

Set Implicit Arguments.
Unset Strict Implicit.

(* Categorie avec exponentiels *)

Section expo_def.

Variables (C : Category) (C1 : HasBinProd C) (a b : C).

 Section expo_laws.

 Variables (Expo : C) (Eval : H_obj_prod C1 Expo a --> b)
   (Op : forall c : C, Map (H_obj_prod C1 c a --> b) (c --> Expo)).

 Definition Lambda_expo (c : C) (f : H_obj_prod C1 c a --> b) := Op c f.

 Definition Beta_rule_law :=
   forall (c : C) (f : H_obj_prod C1 c a --> b),
   Mor_prod C1 (Lambda_expo f) (Id a) o Eval =_S f.

 Definition Eta_rule_law :=
   forall (c : C) (h : c --> Expo),
   Lambda_expo (Mor_prod C1 h (Id a) o Eval) =_S h.

 End expo_laws.

Structure Exponent : Type := 
  {Expo : C;
   Eval : H_obj_prod C1 Expo a --> b;
   Op_lambda : forall c : C, Map (H_obj_prod C1 c a --> b) (c --> Expo);
   Prf_beta_rule : Beta_rule_law Eval Op_lambda;
   Prf_eta_rule : Eta_rule_law Eval Op_lambda}.

Variable e : Exponent.

Definition Lambda (c : C) (f : H_obj_prod C1 c a --> b) := Op_lambda e c f.

End expo_def.

Definition HasExponent (C : Category) (C1 : HasBinProd C) :=
  forall a b : C, Exponent C1 a b.

Section hasexponent_proj.

Variables (C : Category) (C1 : HasBinProd C) (C2 : HasExponent C1) (a b : C).

Definition H_expo := Expo (C2 a b).

Definition H_eval := (Eval (C2 a b)).

Definition H_lambda (c : C) (f : H_obj_prod C1 c a --> b) :=
  Lambda (C2 a b) f.

End hasexponent_proj.

