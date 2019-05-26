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
(*          Basic Category Theory: epic, monic, iso in SET                   *)
(*                                                                           *)
(*          Amokrane Saibi,  May 1994                                        *)
(*                                                                           *)
(*****************************************************************************)


Require Export SET.
Require Export CatProperty.
Require Export MapProperty.

Set Implicit Arguments.
Unset Strict Implicit.

(* Epic <-> Surj *)

SubClass SET_Epic_law (A B : Setoid) (f : Map A B) := Epic_law f.

SubClass SET_Monic_law (A B : Setoid) (f : Map A B) := Monic_law f.

Section set_epic_monic.

Variables (A B : Setoid) (f : Map A B).

Lemma Surj_epic : forall h : B -> A, Surj_law f h -> SET_Epic_law f.
Proof.
intros h H; unfold Surj_law, SET_Epic_law, Epic_law in |- *;
 intros a f' f'' H1.
simpl in |- *; unfold Ext in |- *; intro x.
apply Trans with (f' (f (h x))).
apply Pres1; apply H.
apply Trans with (f'' (f (h x))).
exact (H1 (h x)).
apply Pres1; apply Sym; apply H.
Qed.


(* On veut montrer que: \forall b\in B, il existe a\in A tq b =f(a)
   sachant que (\forall x\in A, g(f(x))=h(f(x))) => (\forall y\in B, g(y)=h(y)).
   raisonnement par l'absurde: supposons qu'un b n'a aucun ante'cedent.
   soient g et h tq: g(b) /= h(b) et g(z)=h(z) \forall z\in B.
   on a alors (\forall x\in A, g(f(x))=h(f(x))) mais (\forall y\in B, g(y)=h(y))
   faux, contradiction: b a un antecedent 

Lemma epic_surj : (SETisEpic A B f) -> (IsSurj f ?).
*)

(* Monic <-> Inj *)
 
Lemma Inj_monic : Inj_law f -> SET_Monic_law f.
Proof.
unfold Inj_law, SET_Monic_law in |- *; intro H1; unfold Monic_law in |- *.
intros C g h H2; simpl in |- *; unfold Ext in |- *; intro x.
apply H1; exact (H2 x).
Qed.

 Section map_const_fun.

 Variable a : A.

 Definition MapConst_fun (b : B) := a.

 Lemma MapConst_map_law : Map_law MapConst_fun.
 Proof.
 unfold Map_law in |- *; intros x y H; apply Refl.
 Qed.

 Definition MapConst : Map B A := MapConst_map_law.

 End map_const_fun.

Lemma Monic_inj : SET_Monic_law f -> Inj_law f.
Proof.
unfold Monic_law in |- *; intros H1; unfold Inj_law in |- *.
intros x y H2.
generalize (H1 _ (MapConst x) (MapConst y)).
intros H3; exact (H3 (fun z : B => H2) (f x)).
Qed.

End set_epic_monic.


Coercion Surj_epic : Surj_law >-> SET_Epic_law. 

Coercion Inj_monic : Inj_law >-> SET_Monic_law.

Coercion Monic_inj : SET_Monic_law >-> Inj_law.



