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
(*	             Preservation of Limits               		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export Limit.

Set Implicit Arguments.
Unset Strict Implicit.

(* Preservation de limites *)

(* F : J -> C *)
(* T : Delta(r) -> F *)
(* H : C -> D *)
(* T o H : Delta(r) -> F o H *)

Section comp_cone.

Variables (J C D : Category) (c : C) (F : Functor J C) 
  (T : Cone c F) (G : Functor C D).

Definition Comp_cone_tau (i : J) : G c --> (F o_F G) i := FMor G (T i).

(* revient a` prouver que : H(T(j)) = H(T(i)) o H(F g) *)

Lemma Comp_cone_tau_cone_law : Cone_law Comp_cone_tau.
Proof.
unfold Cone_law in |- *; intros i j g; unfold Comp_cone_tau in |- *.
unfold FMor at 3 in |- *; simpl in |- *.
unfold Comp_FMor in |- *.
(* *) apply Trans with (FMor G (T i o FMor F g)).
unfold Comp_FOb in |- *; apply FPres. 
apply (EqC T g).
unfold Comp_FOb in |- *; apply FComp.
Qed.

Definition Comp_cone := Build_Cone Comp_cone_tau_cone_law.

End comp_cone.

Infix "o_C" := Comp_cone (at level 20, right associativity).

(* H : C -> D preserve toutes les limites du foncteur F : J -> C *)

Section def_pres_limits.

Variables (J C D : Category) (F : Functor J C) (G : Functor C D).

Definition Preserves_1limit (l : Limit F) := IsLimit (Limiting_cone l o_C G).

Definition Preserves_limits := forall l : Limit F, Preserves_1limit l.

End def_pres_limits.

Definition Continuous (C D : Category) (G : Functor C D) :=
  forall (J : Category) (F : Functor J C), Preserves_limits F G.