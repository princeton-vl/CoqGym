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



Require Export Relations.

Set Implicit Arguments.
Unset Strict Implicit.

(* evite le clash d'univers entre le setoide des foncteur et SET *)
  
(***  SETOID  ***)

Structure > Setoid' : Type := 
  {Carrier' :> Type;
   Equal' : Relation Carrier';
   Prf_equiv' :> Equivalence Equal'}.

Infix "=_S'" := Equal' (at level 70).

(*** rewrite rules ***)

Lemma Refl' : forall (S : Setoid') (x : S), x =_S' x.
Proof.
intro S; exact (Prf_refl S).
Qed.

Lemma Sym' : forall (S : Setoid') (x y : S), x =_S' y -> y =_S' x.
Proof.
intro S; exact (Prf_sym S).
Qed.

Lemma Trans' :
 forall (S : Setoid') (x y z : S), x =_S' y -> y =_S' z -> x =_S' z.
Proof.
intro S; exact (Prf_trans S).
Qed.

(* *)

(***  MAP  ***)

Section maps'.

Variable A B : Setoid'.

Definition Map_law' (f : A -> B) := forall x y : A, x =_S' y -> f x =_S' f y.

Structure > Map' : Type :=  {Ap' :> A -> B; Pres' :> Map_law' Ap'}.

(*** rewrite rule ***)

Lemma Pres1' : forall (m : Map') (x y : A), x =_S' y -> m x =_S' m y.
Proof.
exact Pres'.
Qed.

(* *)

Definition Ext' (f g : Map') := forall x : A, f x =_S' g x.

Lemma Ext_equiv' : Equivalence Ext'.
Proof.
intros; apply Build_Equivalence.
unfold Reflexive in |- *; unfold Ext' in |- *; intros f x.
apply Refl'.
apply Build_Partial_equivalence.
unfold Transitive in |- *; unfold Ext' in |- *; intros f g h e1 e2 x.
(* *) apply Trans' with (g x).
apply (e1 x).
apply (e2 x).
unfold Symmetric in |- *; unfold Ext' in |- *; intros f g e x.
apply Sym'; trivial.
Qed.

Canonical Structure Map_setoid' : Setoid' := Ext_equiv'.

End maps'.

(*** MAP2 ***)

Section fun2_to_map2'.

Variable A B C : Setoid'.

Definition Map2' := Map' A (Map_setoid' B C).

Variable f : A -> B -> C.

Definition Map2_congl_law' :=
  forall (b1 b2 : B) (a : A), b1 =_S' b2 -> f a b1 =_S' f a b2.

Definition Map2_congr_law' :=
  forall (a1 a2 : A) (b : B), a1 =_S' a2 -> f a1 b =_S' f a2 b.

Definition Map2_cong_law' :=
  forall (a1 a2 : A) (b1 b2 : B),
  a1 =_S' a2 -> b1 =_S' b2 -> f a1 b1 =_S' f a2 b2.

Hypothesis pgcl : Map2_congl_law'.
Hypothesis pgcr : Map2_congr_law'.

Lemma Map2_map_law1' : forall a : A, Map_law' (f a).
Proof.
intro a; unfold Map_law' in |- *.
intros b1 b2 H; apply (pgcl a H).
Qed.

Canonical Structure Map2_map1' (a : A) := Build_Map' (Map2_map_law1' a).

Lemma Map2_map_law2' : Map_law' Map2_map1'.
Proof.
unfold Map_law', Map2_map1' in |- *.
intros a1 a2 H; simpl in |- *; unfold Ext' in |- *; intro b; simpl in |- *.
apply pgcr; trivial.
Qed.

Definition Build_Map2' : Map2' := Build_Map' Map2_map_law2'.

End fun2_to_map2'.


Section prop_map2'.

Variables (A B C : Setoid') (f : Map2' A B C).

Definition Ap2' (a : A) (b : B) := f a b.

Lemma Prf_map2_congl' : Map2_congl_law' Ap2'.
Proof.
unfold Map2_congl_law' in |- *; intros b1 b2 a H.
unfold Ap2' in |- *; apply (Pres1' (f a)); trivial.
Qed.

Lemma Prf_map2_congr' : Map2_congr_law' Ap2'.
Proof.
unfold Map2_congr_law' in |- *; intros a1 a2 b H.
apply (Pres1' f H b).
Qed.

Lemma Prf_map2_cong' : Map2_cong_law' Ap2'.
Proof.
unfold Map2_cong_law' in |- *; intros a1 a2 b1 b2 H1 H2.
(* *) apply Trans' with (Ap2' a2 b1).
apply (Prf_map2_congr' b1 H1).
apply (Prf_map2_congl' a2 H2).
Qed.

End prop_map2'.

Coercion Ap2' : Map2' >-> Funclass.

Identity Coercion Map2'_Map' : Map2' >-> Map'.


