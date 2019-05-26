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
(*          Categories                                                       *)
(*                                                                           *)
(*          Peter Aczel, Dec. 92                                             *)
(*          rev. Gerard Huet,  Aug. 1993                                     *)
(*          rev. Amokrane Saibi,  May 1994                                   *)
(*                                                                           *)
(*****************************************************************************)

Require Export Map2.

Set Implicit Arguments.
Unset Strict Implicit.

(*  The type of categories *)

Section cat.

Variables (Ob : Type) (Hom : Ob -> Ob -> Setoid).

Infix "-->" := Hom (at level 95, right associativity).

Variable Op_comp : forall a b c : Ob, Map2 (a --> b) (b --> c) (a --> c).

Definition Cat_comp (a b c : Ob) (f : a --> b) (g : b --> c) :=
  Op_comp a b c f g.

Infix "o" := Cat_comp (at level 20, right associativity).

Definition Assoc_law :=
  forall (a b c d : Ob) (f : a --> b) (g : b --> c) (h : c --> d),
  f o g o h =_S (f o g) o h.

Variable Id : forall a : Ob, a --> a.

Definition Idl_law := forall (a b : Ob) (f : a --> b), Id _ o f =_S f.

Definition Idr_law := forall (a b : Ob) (f : b --> a), f =_S f o Id _.

End cat.

Structure Category : Type := 
  {Ob :> Type;
   Hom : Ob -> Ob -> Setoid;
   Op_comp : forall a b c : Ob, Map2 (Hom a b) (Hom b c) (Hom a c);
   Id : forall a : Ob, Hom a a;
   Prf_ass : Assoc_law Op_comp;
   Prf_idl : Idl_law Op_comp Id;
   Prf_idr : Idr_law Op_comp Id}.

(* Projections *)

Definition Comp (C : Category) := Cat_comp (Op_comp (c:=C)).

Infix "-->" := Hom (at level 95, right associativity).
Infix "o" := Comp (at level 20, right associativity).

(*** rewrite rules ***)

Lemma Ass :
 forall (C : Category) (a b c d : C) (f : a --> b) 
   (g : b --> c) (h : c --> d), f o g o h =_S (f o g) o h.
Proof.
exact Prf_ass.
Qed.

Lemma Ass1 :
 forall (C : Category) (a b c d : C) (f : a --> b) 
   (g : b --> c) (h : c --> d), (f o g) o h =_S f o g o h.
Proof.
intros C a b c d f g h; apply Sym; apply Ass.
Qed.

Lemma Idl : forall (C : Category) (a b : C) (f : a --> b), Id _ o f =_S f.
Proof.
exact Prf_idl.
Qed.

Lemma Idl1 : forall (C : Category) (a b : C) (f : a --> b), f =_S Id _ o f.
Proof.
intros C a b f; apply Sym; apply Idl.
Qed.

Lemma Idr : forall (C : Category) (a b : C) (f : b --> a), f =_S f o Id _.
Proof.
exact Prf_idr.
Qed.

Lemma Idr1 : forall (C : Category) (a b : C) (f : a --> b), f o Id _ =_S f.
Proof.
intros C a b f; apply Sym; apply Idr.
Qed.

Lemma Idrl :
 forall (C : Category) (a b : C) (f : a --> b), f o Id _ =_S Id _ o f.
Proof.
intros C a b f; apply Trans with f.
apply Idr1.
apply Idl1.
Qed.

Lemma Idlr :
 forall (C : Category) (a b : C) (f : a --> b), Id _ o f =_S f o Id _.
Proof.
intros C a b f; apply Trans with f.
apply Idl.
apply Idr.
Qed.

(* *)

(* construire un ope'rateur de composition a` partir d'une
   fonction de composition *)

Section composition_to_operator.

Variables (A : Type) (H : A -> A -> Setoid)
  (Cfun : forall a b c : A, H a b -> H b c -> H a c).

Definition Congl_law :=
  forall (a b c : A) (f g : H b c) (h : H a b),
  f =_S g -> Cfun h f =_S Cfun h g. 

Definition Congr_law :=
  forall (a b c : A) (f g : H a b) (h : H b c),
  f =_S g -> Cfun f h =_S Cfun g h. 

Definition Cong_law :=
  forall (a b c : A) (f f' : H a b) (g g' : H b c),
  f =_S f' -> g =_S g' -> Cfun f g =_S Cfun f' g'. 

Hypothesis pcgl : Congl_law.
Hypothesis pcgr : Congr_law.

Variable a b c : A.

Definition Build_Comp :=
  Build_Map2 (pcgl (a:=a) (b:=b) (c:=c)) (pcgr (a:=a) (b:=b) (c:=c)).

End composition_to_operator.


(*** rewrite rules ***)

Section cat_cong.

Variable C : Category.

Lemma Comp_l :
 forall (a b c : C) (f g : b --> c) (h : a --> b), f =_S g -> h o f =_S h o g. 
Proof.
intros; unfold Comp, Cat_comp in |- *; apply Map2_l; trivial.
Qed.

Lemma Comp_r :
 forall (a b c : C) (f g : a --> b) (h : b --> c), f =_S g -> f o h =_S g o h. 

Proof.
intros; unfold Comp, Cat_comp in |- *; apply Map2_r; trivial.
Qed.

Lemma Comp_lr :
 forall (a b c : C) (f f' : a --> b) (g g' : b --> c),
 f =_S f' -> g =_S g' -> f o g =_S f' o g'. 

Proof.
intros; unfold Comp, Cat_comp in |- *; apply Map2_lr; trivial.
Qed.

End cat_cong.

(* *)
