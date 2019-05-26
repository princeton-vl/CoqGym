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
(*          Category Product                                                 *)
(*                                                                           *)
(*          Amokrane Saibi,  May 1994                                        *)
(*                                                                           *)
(*****************************************************************************)


Require Export Category. 
Require Export SetoidPROD.

Set Implicit Arguments.
Unset Strict Implicit.

Section ProdCat.

Variable A B : Category.

Structure POb : Type :=  {Ob_l : A; Ob_r : B}.

 Section pmor_setoid_def.

 Variable u t : POb.

 Structure Pmor : Type := 
   {Hom_l : Ob_l u --> Ob_l t; Hom_r : Ob_r u --> Ob_r t}.

 Definition Equal_Pmor (f g : Pmor) :=
   Hom_l f =_S Hom_l g /\ Hom_r f =_S Hom_r g.

 Lemma Equal_Pmor_equiv : Equivalence Equal_Pmor.
 Proof.
 apply Build_Equivalence.
 unfold Reflexive, Equal_Pmor in |- *; intro x; split; apply Refl.  
 apply Build_Partial_equivalence.
 unfold Transitive, Equal_Pmor in |- *; intros x1 x2 x3 H H0.
 elim H; intros H1 H2; elim H0; intros H3 H4; split.
 (* *) apply Trans with (Hom_l x2); assumption.
 (* *) apply Trans with (Hom_r x2); assumption.
 unfold Symmetric, Equal_Pmor in |- *; intros x1 x2 H.
 elim H; intros H1 H2; split; apply Sym; assumption.
 Qed.

 Canonical Structure Prod_Hom : Setoid := Equal_Pmor_equiv.

 Definition Prod_Hom' := SPROD (Ob_l u --> Ob_l t) (Ob_r u --> Ob_r t).

 Definition Build1_Pmor :
   (Ob_l u --> Ob_l t) -> (Ob_r u --> Ob_r t) -> Prod_Hom := Build_Pmor.
                
 End pmor_setoid_def.

(* composition *)

Definition Comp_Pmor (a b c : POb) (f : Prod_Hom a b) 
  (g : Prod_Hom b c) := Build_Pmor (Hom_l f o Hom_l g) (Hom_r f o Hom_r g).

Lemma Comp_Pmor_congl : Congl_law Comp_Pmor.
Proof.
unfold Congl_law in |- *; simpl in |- *.
unfold Equal_Pmor, Comp_Pmor in |- *; simpl in |- *.
intros a b c f g h H. 
elim H; intros H1 H2; split; apply Comp_l; assumption.
Qed.

Lemma Comp_Pmor_congr : Congr_law Comp_Pmor.
Proof.
unfold Congr_law in |- *; simpl in |- *.
unfold Equal_Pmor, Comp_Pmor in |- *; simpl in |- *.
intros a b c f g.
elim f; elim g; simpl in |- *.
intros gl gr fl fr H h.
elim h; simpl in |- *.
intros hl hr.
elim H; intros H1 H2; split; apply Comp_r; assumption.
Qed.

Definition Comp_PROD := Build_Comp Comp_Pmor_congl Comp_Pmor_congr.

Lemma Assoc_PROD : Assoc_law Comp_PROD.
Proof.
unfold Assoc_law in |- *; simpl in |- *.
unfold Equal_Pmor in |- *; simpl in |- *.
intros; split; apply Ass.
Qed.

Definition Id_PROD (a : POb) := Build_Pmor (Id (Ob_l a)) (Id (Ob_r a)).

Lemma Idl_PROD : Idl_law Comp_PROD Id_PROD.
Proof.
unfold Idl_law in |- *; simpl in |- *.
unfold Equal_Pmor in |- *; simpl in |- *.
intros; split; apply Idl.
Qed.
 
Lemma Idr_PROD : Idr_law Comp_PROD Id_PROD.
Proof.
unfold Idr_law in |- *; simpl in |- *.
unfold Equal_Pmor in |- *; simpl in |- *.
intros; split; apply Idr. 
Qed.
 
Canonical Structure PROD := Build_Category Assoc_PROD Idl_PROD Idr_PROD.

End ProdCat.
