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


(** %\subsection*{ support :  Map2.v }%*)
(** This file introduces [Map2] which is to [A->B->C] like [Map] is to [A->B]
 Similarly a setoid [MAP2] is introduced and we have tools for (un)currying 
 and using / filling in arguments. This is not linear algebra-specific and 
 could all have been done inside the  algebra contribution; it just facilitates
 using fuctions of two arguments *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Export equal_syntax.
From Algebra Require Export Cartesian.

(* We have setoid-compatible functions called "Map" *)

(* These are 1-ary functions; more general n-ary functions are defined by *)
(* (un)currying, (repeatedly) using (cart A B), the cartesian product *)
(* setoid construction. Still, it's nicer to have a more direct way of *)
(* dealing with 2-ary functions because these occur relatively often. *)

(* I call these "Map2" - and here I provide also tools to jump between *)
(* the two representations. *)

(** %\label{Map2}% *)
Record Map2 (A B C : Setoid) : Type := 
  {Ap2 :> A -> B -> C; Ap2_comp_proof : fun2_compatible Ap2}.


Definition Map2_Mapcart :
  forall A B C : Setoid, Map2 A B C -> Map (cart A B) C.
intros.
apply (Build_Map (Ap:=fun ab : cart A B => X (proj1 ab) (proj2 ab))).
red in |- *.
intros.
elim X.
intros.
red in Ap2_comp_proof0.
simpl in |- *.
apply Ap2_comp_proof0; auto with algebra.
Defined.

Definition Mapcart_Map2 :
  forall A B C : Setoid, Map (cart A B) C -> Map2 A B C.
intros.
apply (Build_Map2 (Ap2:=fun (a : A) (b : B) => X (couple a b))).
red in |- *.
intros.
apply Ap_comp; auto with algebra.
Defined.


(* The setoid of 2-ary functions *)
Definition MAP2 (A B C : Setoid) : Setoid.
intros.
apply
 (Build_Setoid
    (Equal:=fun f g : Map2 A B C =>
            forall (a a' : A) (b b' : B),
            a =' a' in _ -> b =' b' in _ -> f a b =' g a' b' in _)).
split; try split; red in |- *; unfold app_rel in |- *.
intros; destruct x.
simpl in |- *.
apply Ap2_comp_proof0; auto with algebra.
intros.
apply Trans with (y a b); auto with algebra.
intros.
apply Sym; auto with algebra.
Defined.


(* Tools for filling in first and second arguments. *)
Definition Map2_ap_Map : forall A B C : Setoid, Map2 A B C -> A -> MAP B C.
intros.
apply (Build_Map (Ap:=X X0)).
destruct X; red in |- *; simpl in |- *.
intros.
apply Ap2_comp_proof0; auto with algebra.
Defined.

Definition Ap2_Map : forall A B C : Setoid, Map2 A B C -> Map A (MAP B C).
intros.
apply (Build_Map (Ap:=fun a => Map2_ap_Map X a)).
red in |- *.
intros; simpl in |- *.
red in |- *; simpl in |- *.
intros; destruct X.
simpl in |- *.
apply Ap2_comp_proof0; auto with algebra.
Defined.

Definition Map2_ap'_Map : forall A B C : Setoid, Map2 A B C -> B -> MAP A C.
intros.
apply (Build_Map (Ap:=fun a => X a X0)).
destruct X; red in |- *; simpl in |- *.
intros.
apply Ap2_comp_proof0; auto with algebra.
Defined.

Definition Ap2_Map' : forall A B C : Setoid, Map2 A B C -> Map B (MAP A C).
intros.
apply (Build_Map (Ap:=fun b => Map2_ap'_Map X b)).
red in |- *.
intros; simpl in |- *.
red in |- *; simpl in |- *.
intros; destruct X.
simpl in |- *.
apply Ap2_comp_proof0; auto with algebra.
Defined.
