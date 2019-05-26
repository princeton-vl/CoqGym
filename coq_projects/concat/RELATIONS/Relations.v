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


(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*                               Oct 1st 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                               Relations.v                                *)
(****************************************************************************)

(*****************************************************************************)
(*          Projet Formel - Calculus of Inductive Constructions V5.10        *)
(*****************************************************************************)
(*									     *)
(*	    Relations over a Type : Orderings              		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*          F. Prost, G. Kahn, G. Huet	May 94				     *)
(*									     *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Section Orderings.

Variable U : Type.
   
Definition Relation := U -> U -> Prop.

Variable R : Relation.
   
Definition Reflexive := forall x : U, R x x.
   
Definition Transitive := forall x y z : U, R x y -> R y z -> R x z.
   
Definition Symmetric := forall x y : U, R x y -> R y x.
   
Definition Antisymmetric := forall x y : U, R x y -> R y x -> x = y.
   
Definition Contains (R R' : Relation) := forall x y : U, R' x y -> R x y.
   
Definition Same_relation (R R' : Relation) := Contains R R' /\ Contains R' R.

Structure Preorder : Prop := 
  {Prf_refl1 : Reflexive; Prf_trans1 : Transitive}.
   
Structure Order : Prop := 
  {Prf_preorder :> Preorder; Prf_asym : Antisymmetric}.
   
Structure Partial_equivalence : Prop := 
  {Prf_trans : Transitive; Prf_sym : Symmetric}.
   
Structure Equivalence : Prop := 
  {Prf_refl : Reflexive; Prf_pequiv :> Partial_equivalence}.
   
Canonical Structure Equiv_preorder (e : Equivalence) :=
  Build_Preorder (Prf_refl e) (Prf_trans e).
   
Coercion Equiv_preorder : Equivalence >-> Preorder.

End Orderings.

Hint Unfold Reflexive.
Hint Unfold Transitive.
Hint Unfold Antisymmetric.
Hint Unfold Symmetric.
Hint Unfold Contains.
Hint Unfold Same_relation.
Hint Resolve Build_Preorder.
Hint Resolve Build_Order.
Hint Resolve Build_Equivalence.
Hint Resolve Build_Partial_equivalence.



