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
(*	                      Comma Category (x|G)            		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(* (x|G) *)

Section comma_def.

Variables (A X : Category) (G : Functor A X) (x : X).

Structure Com_ob : Type :=  {Ob_com_ob : A; Mor_com_ob : x --> G Ob_com_ob}.

 Section com_arrow_def.

 Variable axf bxg : Com_ob.
 
 Definition Com_law (h : Ob_com_ob axf --> Ob_com_ob bxg) :=
   Mor_com_ob bxg =_S Mor_com_ob axf o FMor G h.

 Structure > Com_arrow : Type := 
   {Mor_com_arrow : Ob_com_ob axf --> Ob_com_ob bxg;
    Prf_com_law :> Com_law Mor_com_arrow}.

 (*** rewrite rules ***)

 (* *)

 Definition Equal_com_arrow (h h' : Com_arrow) :=
   Mor_com_arrow h =_S Mor_com_arrow h'.

 Lemma Equal_com_arrow_equiv : Equivalence Equal_com_arrow.
 Proof.
 apply Build_Equivalence; unfold Equal_com_arrow in |- *.
 unfold Reflexive in |- *; intro f.
 apply Refl.
 apply Build_Partial_equivalence.
 unfold Transitive in |- *; intros f g h H1 H2.
 (* *) apply Trans with (Mor_com_arrow g); assumption. 
 unfold Symmetric in |- *; intros f g H.
 apply Sym; assumption.
 Qed.

 Canonical Structure Com_arrow_setoid : Setoid := Equal_com_arrow_equiv.

 End com_arrow_def. 

(* composition of two arrows in comma *)

 Section comp_com_def.

 Variables (axf bxg cxh : Com_ob) (f : Com_arrow axf bxg)
   (g : Com_arrow bxg cxh).

 Definition Comp_com_mor := Mor_com_arrow f o Mor_com_arrow g.

 Lemma Comp_com_law : Com_law Comp_com_mor.
 Proof.
 unfold Com_law, Comp_com_mor in |- *.
 (* *) apply Trans with (Mor_com_ob bxg o FMor G (Mor_com_arrow g)).
 apply (Prf_com_law g).
 (* *) apply
        Trans
         with
           (Mor_com_ob axf
            o FMor G (Mor_com_arrow f) o FMor G (Mor_com_arrow g)).
 (* *) apply
        Trans
         with
           ((Mor_com_ob axf o FMor G (Mor_com_arrow f))
            o FMor G (Mor_com_arrow g)).
 apply Comp_r; apply (Prf_com_law f).
 apply Ass1.
 apply Comp_l; apply FComp1.
 Qed.

 Canonical Structure Comp_com_arrow := Build_Com_arrow Comp_com_law.

 End comp_com_def.
 
(* composition operator *)

Lemma Comp_com_congl : Congl_law Comp_com_arrow.
Proof.
unfold Congl_law in |- *; simpl in |- *.
intros a b c f1; elim f1; intros h e f2.
elim f2; intros h' e' f3; elim f3; intros h'' e''.
unfold Equal_com_arrow in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
intro H; apply Comp_l; trivial.
Qed.

Lemma Comp_com_congr : Congr_law Comp_com_arrow.
Proof.
unfold Congr_law in |- *; simpl in |- *.
intros a b c f1; elim f1; intros h e f2.
elim f2; intros h' e' f3; elim f3; intros h'' e''.
unfold Equal_com_arrow in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
intro H; apply Comp_r; trivial.
Qed.

Definition Comp_Comma := Build_Comp Comp_com_congl Comp_com_congr. 

Lemma Assoc_Comma : Assoc_law Comp_Comma.
Proof.
unfold Assoc_law in |- *; intros a b c d f1; elim f1.
intros h1 e1 f2; elim f2; intros h2 e2 f3.
elim f3; intros h3 e3.
simpl in |- *; unfold Equal_com_arrow in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
apply Ass.
Qed.

(* Id *)

Lemma Id_com_law : forall axf : Com_ob, Com_law (Id (Ob_com_ob axf)).
Proof.
intro axf; unfold Com_law in |- *.
(* *) apply Trans with (Mor_com_ob axf o Id (G (Ob_com_ob axf))).
apply Idr.
apply Comp_l; apply FId1.
Qed.

Canonical Structure Id_Comma (axf : Com_ob) :=
  Build_Com_arrow (Id_com_law axf).

Lemma Idl_Comma : Idl_law Comp_Comma Id_Comma.
Proof.
unfold Idl_law in |- *; intros a b f1; elim f1; intros h e.
simpl in |- *; unfold Equal_com_arrow in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
apply Idl.
Qed.

Lemma Idr_Comma : Idr_law Comp_Comma Id_Comma.
Proof.
unfold Idr_law in |- *; intros a b f1; elim f1; intros h e.
simpl in |- *; unfold Equal_com_arrow in |- *; simpl in |- *.
unfold Comp_com_mor in |- *; simpl in |- *.
apply Idr.
Qed.

Canonical Structure Comma := Build_Category Assoc_Comma Idl_Comma Idr_Comma.

End comma_def.