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
(*          Category Theory : Functors                                       *)
(*                                                                           *)
(*          Amokrane Saibi May 1994                                          *)
(*                                                                           *)
(*****************************************************************************)

Require Export Setoid_dup1.
Require Export Hom_Equality.

Set Implicit Arguments.
Unset Strict Implicit.

(* Functors *) 

Section funct_def.

Variable C D : Category.

 Section funct_laws.

 Variables (FOb : C -> D)
   (FMap : forall a b : C, Map (a --> b) (FOb a --> FOb b)).

 Definition Fcomp_law :=
   forall (a b c : C) (f : a --> b) (g : b --> c),
   FMap a c (f o g) =_S FMap a b f o FMap b c g.

 Definition Fid_law := forall a : C, FMap a a (Id a) =_S Id (FOb a).

 End funct_laws.

Structure Functor : Type := 
  {FOb :> C -> D;
   FMap : forall a b : C, Map (a --> b) (FOb a --> FOb b);
   Prf_Fcomp_law : Fcomp_law FMap;
   Prf_Fid_law : Fid_law FMap}.

Definition FMor (F : Functor) (a b : C) (f : a --> b) := FMap F a b f.

(*** rewrite rules ***)

Lemma FPres :
 forall (F : Functor) (a b : C) (f g : a --> b),
 f =_S g -> FMor F f =_S FMor F g.
Proof.
intros F a b; exact (Pres (FMap F a b)).
Qed.

Lemma FComp :
 forall (F : Functor) (a b c : C) (f : a --> b) (g : b --> c),
 FMor F (f o g) =_S FMor F f o FMor F g.
Proof.
exact Prf_Fcomp_law.
Qed.

Lemma FComp1 :
 forall (F : Functor) (a b c : C) (f : a --> b) (g : b --> c),
 FMor F f o FMor F g =_S FMor F (f o g).
Proof.
intros; apply Sym; apply (Prf_Fcomp_law F f g).
Qed.

Lemma FId : forall (F : Functor) (a : C), FMor F (Id a) =_S Id (FOb F a).
Proof.
exact Prf_Fid_law.
Qed.

Lemma FId1 : forall (F : Functor) (a : C), Id (FOb F a) =_S FMor F (Id a).
Proof.
intros; apply Sym; apply (Prf_Fid_law F a).
Qed.

(* *)

End funct_def.

(* Functors equality *)

Section funct_setoid.

Variable C D : Category. 

Definition Equal_Functor (F G : Functor C D) :=
  forall (a b : C) (f : a --> b), FMor F f =_H FMor G f.

Lemma Equal_Functor_equiv : Equivalence Equal_Functor.
Proof.
apply Build_Equivalence; unfold Equal_Functor in |- *.
auto.
apply Build_Partial_equivalence.
unfold Transitive in |- *; intros F G H Ass1 Ass2 a b f.
(* *) apply Equal_hom_trans with (G a) (G b) (FMor G f); auto.
auto.
Qed.

Canonical Structure Functor_setoid := Build_Setoid' Equal_Functor_equiv.

End funct_setoid.

Infix "=_F" := Equal_Functor (at level 70).


(* composition of two functors *)

Section Comp_F.

Variables (C D E : Category) (G : Functor C D) (H : Functor D E).

Definition Comp_FOb (a : C) := H (G a).

 Section comp_functor_map.

 Variable a b : C.

 Definition Comp_FMor (f : a --> b) := FMor H (FMor G f). 

 Lemma Comp_FMap_law : Map_law Comp_FMor.
 Proof.
 unfold Map_law, Comp_FMor, FMor in |- *; intros f g eqfg.
 apply Pres1; apply Pres1; assumption.
 Qed.

 Definition Comp_FMap :=
   Build_Map (B:=Comp_FOb a --> Comp_FOb b) Comp_FMap_law.

 End comp_functor_map.

Lemma Comp_Functor_comp_law : Fcomp_law Comp_FMap.
Proof.
unfold Fcomp_law, Comp_FOb, Comp_FMap, Comp_FMor in |- *.
simpl in |- *; intros a b c f g.
(* H(G(fog)) = H(G(f)))o(H(G(g)) *) 
(* *) apply Trans with (FMor H (FMor G f o FMor G g)).
(* H(G(fog)) = H(G(f)oG(g)) *)
(* G(fog) = G(f)oG(g) *)
apply FPres; apply FComp.
(* H(G(f)o(G g)) = H(G(f))oH(G(g)) *)
apply FComp.
Qed.

Lemma Comp_Functor_id_law : Fid_law Comp_FMap.
Proof.
unfold Fid_law, Comp_FOb, Comp_FMap, Comp_FMor in |- *.
simpl in |- *; intro a.
(* H(G(Id(a))) = Id(H(G(a))) *)
(* *) apply Trans with (FMor H (Id (G a))).
(* H(G(Id(a))) = H(Id(G(a))) *)
(* G(Id(a)) = Id(G(a)) *)
apply FPres; apply FId.
(* H(Id(G(a))) = Id(H(G(a))) *)
apply FId.
Qed.               

Canonical Structure Comp_Functor :=
  Build_Functor Comp_Functor_comp_law Comp_Functor_id_law.

End Comp_F.

Infix "o_F" := Comp_Functor (at level 20, right associativity).
