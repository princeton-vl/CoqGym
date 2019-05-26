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
(*	                   SET is Complete                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)


Require Export SET.
Require Export Single.
Require Export Limit.
Require Export Map0_dup1.

Set Implicit Arguments.
Unset Strict Implicit.

Section set_c.

Variables (J : Category) (F : Functor J SET).

Definition SET_lim := Cones Single F.

 Section set_lcone_tau_def.

 Variable i : J.

 Definition SET_lcone_tau_fun (sigma : SET_lim) := sigma i Elt.

 Lemma SET_lcone_tau_map_law : Map_law''0 SET_lcone_tau_fun.
 Proof.
 unfold Map_law''0 in |- *; intros s1 s2 H.
 unfold SET_lcone_tau_fun in |- *.
 apply (H i Elt).
 Qed.

 Canonical Structure SET_lcone_tau := Build_Map''0 SET_lcone_tau_map_law.

 End set_lcone_tau_def.

Lemma SET_lcone_cone_law :
 forall (i j : J) (g : i --> j) (tau : SET_lim),
 SET_lcone_tau j tau =_S FMor F g (SET_lcone_tau i tau).
Proof.
intros i j g sigma.
unfold SET_lcone_tau in |- *; simpl in |- *; unfold SET_lcone_tau_fun in |- *.
apply (EqC sigma g Elt).
Qed.

(* construction tau# pour tout tau : DElta(X) -> F *)

 Section set_diese.

 Variables (X : SET) (tau : Cones X F).

  Section set_diese1_def.

  Variable x : X.

   Section set_diese1_tau_def.

   Variable i : J.

   (* (h(x)i)(Elt) =  tau(i)(x) *)

   Definition SET_diese1_tau_fun (a : Single) :=
     match a with
     | Elt => tau i x
     end.

   Lemma SET_diese1_tau_map_law : Map_law SET_diese1_tau_fun.
   Proof.
   unfold Map_law in |- *.
   intros a b; elim a; elim b; simpl in |- *; intro H.
   apply Refl.
   Qed.

   Canonical Structure SET_diese1_tau := Build_Map SET_diese1_tau_map_law.
 
   End set_diese1_tau_def.

 (* h(x) : DElta({*}) -> F *)

  Lemma SET_diese1_tau_cone_law : Cone_law SET_diese1_tau.
  Proof.
  unfold Cone_law in |- *; intros i j g; simpl in |- *.
  unfold Ext in |- *; simpl in |- *.
  intro a; elim a; simpl in |- *.
  unfold Comp_fun in |- *; simpl in |- *.
  apply (EqC tau g x).
  Qed.

  Definition SET_diese1 : SET_lim := Build_Cone SET_diese1_tau_cone_law.

  End set_diese1_def.

 Lemma SET_diese_map_law : Map_law0'' SET_diese1.
 Proof.
 unfold Map_law0'' in |- *; intros x y H; simpl in |- *.
 unfold Equal_NT, SET_diese1 in |- *; simpl in |- *.
 unfold Ext in |- *; simpl in |- *; intros i a.
 elim a; simpl in |- *.
 apply Pres1; trivial.
 Qed.

 Canonical Structure SET_diese := Build_Map0'' SET_diese_map_law.

 End set_diese.
 
(* universalite' *)

Lemma SET_coUAlaw1 :
 forall (X : SET) (tau : Cone X F) (i : J) (x : X),
 tau i x =_S SET_lcone_tau i (SET_diese tau x).
Proof.
simpl in |- *; intros X tau i x.
unfold SET_lcone_tau_fun, SET_diese1 in |- *; simpl in |- *.
apply Refl.
Qed.

Lemma SET_coUAlaw2 :
 forall (X : SET) (tau : Cone X F) (g : Map0'' X SET_lim),
 (forall (i : J) (x : X), tau i x =_S SET_lcone_tau i (g x)) ->
 forall x : X, g x =_S'' SET_diese tau x.
Proof.
intros X tau g H x; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *; intro i; simpl in |- *;
 unfold Ext in |- *; simpl in |- *.
intro e; elim e; simpl in |- *.
apply Sym; apply (H i x).
Qed.

End set_c.