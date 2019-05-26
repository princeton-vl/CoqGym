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
(*	                    Category ONE                  		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Category.

Set Implicit Arguments.
Unset Strict Implicit.

(* The category One *)

Inductive One_ob : Type :=
    Obone : One_ob.

Inductive One_mor : One_ob -> One_ob -> Type :=
    Id_Obone : One_mor Obone Obone.

 Section equal_one_mor.

 Variable a b : One_ob.

 Definition Equal_One_mor (f g : One_mor a b) := True.

 Lemma Equal_One_mor_equiv : Equivalence Equal_One_mor.
 Proof.
 unfold Equal_One_mor in |- *; apply Build_Equivalence;
  [ trivial | apply Build_Partial_equivalence ]; red in |- *; 
  trivial.
 Qed.

 Canonical Structure One_mor_setoid : Setoid := Equal_One_mor_equiv.
 
 End equal_one_mor.

Definition Comp_One_mor (a : One_ob) :=
  let () as x
      return
        (forall b c : One_ob,
         One_mor_setoid x b -> One_mor_setoid b c -> One_mor_setoid x c) :=
      a in
  fun b c =>
  let () as x
      return
        (One_mor_setoid Obone b ->
         One_mor_setoid b x -> One_mor_setoid Obone x) := c in
  fun _ _ => Id_Obone.

Lemma Comp_One_mor_congl : Congl_law Comp_One_mor.
Proof.
unfold Congl_law, Comp_One_mor in |- *; simpl in |- *;
 unfold Equal_One_mor in |- *; trivial.
Qed.

Lemma Comp_One_mor_congr : Congr_law Comp_One_mor.
Proof.
unfold Congr_law, Comp_One_mor in |- *; simpl in |- *;
 unfold Equal_One_mor in |- *; trivial.
Qed.

Definition Comp_One := Build_Comp Comp_One_mor_congl Comp_One_mor_congr.

Lemma Assoc_One : Assoc_law Comp_One.
Proof.
unfold Assoc_law in |- *; simpl in |- *.
unfold Comp_One, Equal_One_mor in |- *; trivial.
Qed.

Definition Id_One (a : One_ob) : One_mor_setoid a a :=
  let () as x return (One_mor x x) := a in Id_Obone.

Lemma Idl_One : Idl_law Comp_One Id_One.
Proof.
unfold Idl_law in |- *; simpl in |- *.
unfold Comp_One, Id_One, Equal_One_mor in |- *; trivial.
Qed.

Lemma Idr_One : Idr_law Comp_One Id_One.
Proof.
unfold Idr_law in |- *; simpl in |- *.
unfold Comp_One, Id_One, Equal_One_mor in |- *; trivial.
Qed.

Canonical Structure One := Build_Category Assoc_One Idl_One Idr_One.

