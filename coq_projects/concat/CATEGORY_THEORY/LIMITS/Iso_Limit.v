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
(*	   Limits  cones(c,F) iso C(c,limF)                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export SET.
Require Export Limit.
Require Export Map0_dup1.

Set Implicit Arguments.
Unset Strict Implicit.

(* cones(c,F) iso C(c,limF) *)


Section iso_cone.

Variables (J C : Category) (F : Functor J C) (l : Limit F) (c : C).

(* Map cones(c,F) vers C(c,limF) *)

Definition PhiCone_fun (tau : Cones c F) := Lim_diese l tau.

Lemma PhiCone_map_law : Map_law''0 PhiCone_fun.
Proof.
unfold Map_law''0, PhiCone_fun in |- *; simpl in |- *.
intros T1 T2 H.
apply (Ldiese_map l); trivial.
Qed.

Canonical Structure PhiCone_map := Build_Map''0 PhiCone_map_law.

(* Map C(c,limF) vers cones(c,F) *)

 Section phicone_1_fun_def.

 Variable f : c --> Lim l.

 Definition PhiCone_1_fun_tau (i : J) := f o Limiting_cone l i.

 Lemma PhiCone_1_fun_cone_law : Cone_law PhiCone_1_fun_tau.
 Proof.
 unfold Cone_law, PhiCone_1_fun_tau in |- *; simpl in |- *.
 intros i j g.
 (* *) apply Trans with (f o Limiting_cone l i o FMor F g).
 apply Comp_l; apply (EqC (Limiting_cone l) g).
 apply Ass.
 Qed.

 Canonical Structure PhiCone_1_fun : Cones c F := PhiCone_1_fun_cone_law.

 End phicone_1_fun_def. 

Lemma PhiCone_1_map_law : Map_law0'' PhiCone_1_fun.
Proof.
unfold Map_law0'', PhiCone_1_fun in |- *. 
intros f g H; simpl in |- *.
unfold Equal_NT in |- *; simpl in |- *.
unfold PhiCone_1_fun_tau in |- *; intro i.
apply Comp_r; trivial.
Qed.

Canonical Structure PhiCone_1_map : Map0'' (c --> Lim l) (Cones c F) :=
  PhiCone_1_map_law.

(* phi et PhiCone_1 sont iso *)

Lemma Lim_areIso : AreBij0'' PhiCone_1_map PhiCone_map.
Proof.
unfold AreBij0'' in |- *; split.
intro f; simpl in |- *; unfold PhiCone_fun in |- *.
apply Sym; apply (Prf_limit2 l).
unfold Limit_eq, PhiCone_1_fun in |- *; simpl in |- *.
intro i; apply Refl.
intro tau; simpl in |- *; unfold Equal_NT in |- *.
unfold PhiCone_1_fun, PhiCone_fun in |- *; simpl in |- *.
intro i; unfold PhiCone_1_fun_tau in |- *.
apply (Prf_limit1 l tau i).
Qed.

End iso_cone.

