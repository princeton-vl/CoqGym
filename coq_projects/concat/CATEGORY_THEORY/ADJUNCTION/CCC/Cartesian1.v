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
(*	                Adjunction Example : Cartesian         		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Diagonal.
Require Export CCC.
Require Export Terminal1.

Set Implicit Arguments.
Unset Strict Implicit.

(* Diag(C) a un RAdj -> C admet les produits *)

Section diag_hasprod1.

Variable C : Category.

SubClass HasBinProd1 := RightAdj (Diag C).

Structure IsCartesian1 : Type := 
  {Car_terminal1 :> Terminal1 C; Car_BP1 :> HasBinProd1}.

Variable H : HasBinProd1.

 Section diag_prod1.

 Variable a b : C.

 Let ua' := CoUnit H (Build_POb a b).

 Definition Obj_prod1 := CoUA_ob ua'.

 Definition Proj1_prod1 := Hom_l (CoUA_mor ua').

 Definition Proj2_prod1 := Hom_r (CoUA_mor ua').

  Section together1_def.

  Variable c : C.

  Definition Together1 (f : c --> a) (g : c --> b) :=
    CoUA_diese ua' (Build_Pmor (u:=Build_POb c c) (t:=Build_POb a b) f g).

  Lemma Together1_l : Map2_congl_law Together1.
  Proof.
  unfold Map2_congl_law in |- *; intros f g g' H'.
  unfold Together1 in |- *.
  apply (Codiese_map ua' (a':=c)).
  simpl in |- *; unfold Equal_Pmor in |- *; simpl in |- *.
  split.
  apply Refl.
  trivial.
  Qed.
 
  Lemma Together1_r : Map2_congr_law Together1.
  Proof.
  unfold Map2_congr_law in |- *; intros f f' g H'.
  unfold Together1 in |- *.
  apply (Codiese_map ua' (a':=c)).
  simpl in |- *; unfold Equal_Pmor in |- *; simpl in |- *.
  split.
  trivial.
  apply Refl.
  Qed.

  Definition Op_together1 := Build_Map2 Together1_l Together1_r.

  End together1_def.

 Lemma Prf_eq1_prod1 : Eq1_prod_law Proj1_prod1 Op_together1. 
 Proof.
 unfold Eq1_prod_law in |- *; intros c f g.
 unfold Together_prod, Op_together1, Together1, Proj1_prod1, Ap2 in |- *;
  simpl in |- *.
 generalize
  (Prf_isCoUA_law1 ua' (Build_Pmor (u:=Build_POb c c) (t:=Build_POb a b) f g)).
 unfold CoUA_eq in |- *; simpl in |- *.
 unfold Equal_Pmor in |- *; simpl in |- *.
 simple induction 1.
 intros H2 H3.
 apply H2.
 Qed. 

 Lemma Prf_eq2_prod1 : Eq2_prod_law Proj2_prod1 Op_together1. 
 Proof.
 unfold Eq2_prod_law in |- *; intros c f g.
 unfold Together_prod, Op_together1, Together1, Proj2_prod1, Ap2 in |- *;
  simpl in |- *.
 generalize
  (Prf_isCoUA_law1 ua' (Build_Pmor (u:=Build_POb c c) (t:=Build_POb a b) f g)).
 unfold CoUA_eq in |- *; simpl in |- *.
 unfold Equal_Pmor in |- *; simpl in |- *.
 simple induction 1.
 intros H2 H3.
 apply H3.
 Qed.

 Lemma Prf_unique_together1 :
  Unique_together_law Proj1_prod1 Proj2_prod1 Op_together1.
 Proof.
 unfold Unique_together_law in |- *; intros c h.
 unfold Together_prod, Ap2 in |- *; simpl in |- *; unfold Together1 in |- *.
 apply Sym.
 apply
  (Prf_isCoUA_law2 ua'
     (f:=Build_Pmor (u:=Build_POb c c) (t:=Build_POb a b) 
           (h o Proj1_prod1) (h o Proj2_prod1)) (g:=h)).
 unfold CoUA_eq in |- *; simpl in |- *.
 unfold Equal_Pmor in |- *; simpl in |- *; split.
 apply Refl.
 apply Refl.
 Qed.

 End diag_prod1.

 Definition BP1_to_BP : HasBinProd C :=
   fun a b : C =>
   Build_BinProd (Prf_eq1_prod1 (a:=a) (b:=b)) (Prf_eq2_prod1 (a:=a) (b:=b))
     (Prf_unique_together1 (a:=a) (b:=b)).

End diag_hasprod1.

Coercion BP1_to_BP : HasBinProd1 >-> HasBinProd.

Coercion Car1_to_Car (C : Category) (H : IsCartesian1 C) :=
  Build_IsCartesian H H.

