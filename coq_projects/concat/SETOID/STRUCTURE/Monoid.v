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
(*                                 Monoid.v                                 *)
(****************************************************************************)


Require Export Map2.

Set Implicit Arguments.
Unset Strict Implicit.

SubClass BinOp (A : Setoid) := Map2 A A A.

Section monoid_laws.

Variables (A : Setoid) (op : BinOp A) (e : A).

Let Ap_op (x y : A) := op x y.

Infix "+_M" := Ap_op (at level 40, left associativity).

Definition Monoid_ass := forall x y z : A, x +_M (y +_M z) =_S x +_M y +_M z.

Definition Monoid_idl := forall x : A, e +_M x =_S x.

Definition Monoid_idr := forall x : A, x =_S x +_M e.

End monoid_laws.

Structure Monoid : Type := 
  {Mcarrier :> Setoid;
   Mop : BinOp Mcarrier;
   Munit : Mcarrier;
   Prf_monoid_ass : Monoid_ass Mop;
   Prf_monoid_idl : Monoid_idl Mop Munit;
   Prf_monoid_idr : Monoid_idr Mop Munit}.

Definition ApMop (m : Monoid) (x y : m) := Mop m x y.

Infix "+_M" := ApMop (at level 40, left associativity).
        

(*** rewrite rules ***)

Lemma Mass :
 forall (M : Monoid) (x y z : M), x +_M (y +_M z) =_S x +_M y +_M z.
Proof.
exact Prf_monoid_ass.
Qed.

Lemma Mass1 :
 forall (M : Monoid) (x y z : M), x +_M y +_M z =_S x +_M (y +_M z).
Proof.
intros; apply Sym; apply Mass.
Qed.

Lemma Midl : forall (M : Monoid) (x : M), Munit M +_M x =_S x.
Proof.
exact Prf_monoid_idl.
Qed.

Lemma Midl1 : forall (M : Monoid) (x : M), x =_S Munit M +_M x.
Proof.
intros; apply Sym; apply Midl.
Qed.

Lemma Midr : forall (M : Monoid) (x : M), x =_S x +_M Munit M.
Proof.          
exact Prf_monoid_idr.
Qed.

Lemma Midr1 : forall (M : Monoid) (x : M), x +_M Munit M =_S x.
Proof.          
intros; apply Sym; apply Midr.
Qed.

(* *)

(* Monoid Morphism *)

Section mon_mors.

Variable m1 m2 : Monoid.

Definition MonUnit_law (f : Map m1 m2) := f (Munit m1) =_S Munit m2.

Definition MonOp_law (f : Map m1 m2) :=
  forall a b : m1, f (a +_M b) =_S f a +_M f b.

Structure MonMor : Type := 
  {MonMap :> Map m1 m2;
   Prf_MonUnit_law : MonUnit_law MonMap;
   Prf_MonOp_law : MonOp_law MonMap}.

(*** rewrite rules ***)

Lemma MMon_unit : forall f : MonMor, f (Munit m1) =_S Munit m2.
Proof.
exact Prf_MonUnit_law.
Qed.

Lemma MMon_op : forall (f : MonMor) (a b : m1), f (a +_M b) =_S f a +_M f b.
Proof.
exact Prf_MonOp_law.
Qed.

(* *)

(* equality of two monoid morphisms *)

Definition Equal_MonMor (f g : MonMor) := f =_M g.

Lemma Equal_MonMor_equiv : Equivalence Equal_MonMor.
Proof.
apply Build_Equivalence.
unfold Reflexive, Equal_MonMor in |- *; intro f.
unfold Ext in |- *; intros x; apply Refl.
apply Build_Partial_equivalence.
unfold Transitive, Equal_MonMor in |- *; intros f g h H1 H2. 
unfold Ext in |- *; intros x.
apply Trans with (g x).
apply (H1 x).
apply (H2 x).
unfold Symmetric, Equal_MonMor in |- *; intros f g H1.
unfold Ext in |- *; intros x.
apply Sym.
apply (H1 x).
Qed.

Canonical Structure MonMor_setoid : Setoid := Equal_MonMor_equiv.

End mon_mors.



