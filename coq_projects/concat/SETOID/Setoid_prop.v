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
(*	                       SubSetoid                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

(* (SubSetoid A P) setoid of elements of A with the property P *)

Require Export Map.

Set Implicit Arguments.
Unset Strict Implicit.

Section sub_setoid.

Variable U : Setoid.

Definition Reg_law (A : U -> Prop) := forall x y : U, x =_S y -> A x -> A y.

Structure > Setoid_pred : Type := 
  {Pred :> U -> Prop; Prf_reg :> Reg_law Pred}.

Variable A : Setoid_pred.

Structure SubType : Type :=  {Elt_sub : U; Prf_constr : A Elt_sub}.

Definition Equal_SubType (a b : SubType) := Elt_sub a =_S Elt_sub b.

Lemma Equal_SubType_equiv : Equivalence Equal_SubType.
Proof.
apply Build_Equivalence.
unfold Reflexive in |- *; intro x; exact (Refl (Elt_sub x)).
apply Build_Partial_equivalence.
unfold Transitive in |- *; intros a b c H1 H2; unfold Equal_SubType in |- *.
apply Trans with (Elt_sub b); auto.
unfold Symmetric in |- *; intros a b H; unfold Equal_SubType in |- *.
apply Sym; auto.
Qed.

Canonical Structure SubSetoid : Setoid := Equal_SubType_equiv.

End sub_setoid.

Section restricted_map.

Variables (A B : Setoid) (f : Map A B) (P : Setoid_pred A).

Definition Restricted_fun (a : SubSetoid P) := f (Elt_sub a).

Lemma Restricted_map_law : Map_law Restricted_fun.
Proof.
unfold Map_law in |- *; simpl in |- *.
unfold Equal_SubType in |- *; intros a1 a2 H.
unfold Restricted_fun in |- *; apply Pres1; trivial.
Qed.

Canonical Structure RestrictedMap := Build_Map Restricted_map_law.

End restricted_map.

