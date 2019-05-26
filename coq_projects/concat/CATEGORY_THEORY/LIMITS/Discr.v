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
(*	  Discrete category (used in the definition of Products) 	     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

(* Discrete Categories *)

Section discrete.

Variable U : Type.

Inductive Discr_mor : U -> U -> Type :=
    Build_Discr_mor : forall a : U, Discr_mor a a.

 Section disc_mor_setoid.

 Variable a b : U.

 Definition Equal_Discr_mor (f g : Discr_mor a b) := True.

 Lemma Equal_Discr_mor_equiv : Equivalence Equal_Discr_mor.
 Proof.
 unfold Equal_Discr_mor in |- *.
 apply Build_Equivalence; [ trivial | apply Build_Partial_equivalence ];
  red in |- *; trivial.
 Qed.

 Canonical Structure Discr_mor_setoid := Build_Setoid Equal_Discr_mor_equiv.

 End disc_mor_setoid.

Definition Comp_Discr_mor (a b c : U) (f : Discr_mor a b) :=
  match f in (Discr_mor d d0) return (Discr_mor d0 c -> Discr_mor d c) with
  | Build_Discr_mor x =>
      fun g : Discr_mor x c =>
      match g in (Discr_mor d d0) return (Discr_mor d d0) with
      | Build_Discr_mor x => Build_Discr_mor x
      end
  end.
   
Lemma Comp_Discr_congl : Congl_law Comp_Discr_mor.
Proof.
unfold Congl_law in |- *; simpl in |- *; unfold Equal_Discr_mor in |- *.
intros a b c f g h H; elim H; trivial.
Qed.

Lemma Comp_Discr_congr : Congr_law Comp_Discr_mor.
Proof.
unfold Congr_law, Comp_Discr_mor in |- *; simpl in |- *;
 unfold Equal_Discr_mor in |- *; trivial.
Qed.

Definition Comp_Discr := Build_Comp Comp_Discr_congl Comp_Discr_congr.

Lemma Assoc_Discr : Assoc_law Comp_Discr.
Proof.
unfold Assoc_law in |- *; simpl in |- *.
unfold Comp_Discr, Equal_Discr_mor in |- *; trivial.
Qed.

Definition Id_Discr (a : U) := Build_Discr_mor a.

Lemma Idl_Discr : Idl_law Comp_Discr Id_Discr.
Proof.
unfold Idl_law in |- *; simpl in |- *.
unfold Comp_Discr, Id_Discr, Equal_Discr_mor in |- *; trivial.
Qed.

Lemma Idr_Discr : Idr_law Comp_Discr Id_Discr.
Proof.
unfold Idr_law in |- *; simpl in |- *.
unfold Comp_Discr, Id_Discr, Equal_Discr_mor in |- *; trivial.
Qed.

(* Bug ds trad *)

Canonical Structure Discr := Build_Category Assoc_Discr Idl_Discr Idr_Discr.

End discrete.

Axiom
  Discr_mor_ind1 :
    forall (U : Type) (a : U) (P : Discr_mor a a -> Prop),
    P (Build_Discr_mor a) -> forall x : Discr_mor a a, P x.





