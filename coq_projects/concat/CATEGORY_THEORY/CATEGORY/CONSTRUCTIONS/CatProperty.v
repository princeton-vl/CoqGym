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
(*          Basic Category Theory: epic, monic, iso                          *)
(*                                                                           *)
(*          Amokrane Saibi,  May 1994                                        *)
(*                                                                           *)
(*****************************************************************************)


Require Export Dual.

Set Implicit Arguments.
Unset Strict Implicit.

Section epic_monic_def.

Variables (C : Category) (a b : C).
 
(* epic *)

Definition Epic_law (f : a --> b) :=
  forall (c : C) (g h : b --> c), f o g =_S f o h -> g =_S h.

Structure > Epic : Type := 
  {Epic_mor : a --> b; Prf_isEpic :> Epic_law Epic_mor}.

(* monic *)

Definition Monic_law (f : b --> a) :=
  forall (c : C) (g h : c --> b), g o f =_S h o f -> g =_S h.

Structure > Monic : Type := 
  {Monic_mor : b --> a; Prf_isMonic :> Monic_law Monic_mor}.

End epic_monic_def.

(* iso *)

Section iso_def.

Variable C : Category.

Definition RIso_law (a b : C) (f : a --> b) (f1 : b --> a) := f1 o f =_S Id b.

Variable a b : C.

Definition AreIsos (f : a --> b) (f1 : b --> a) :=
  RIso_law f f1 /\ RIso_law f1 f.

Structure > Iso : Type := 
  {Iso_mor : a --> b; Inv_iso : b --> a; Prf_Iso :> AreIsos Iso_mor Inv_iso}.

Lemma Idl_inv : forall i : Iso, RIso_law (Iso_mor i) (Inv_iso i).
Proof.
simple induction i; unfold AreIsos in |- *; intros f g p; elim p; auto.
Qed.

Lemma Idr_inv : forall i : Iso, RIso_law (Inv_iso i) (Iso_mor i).
Proof.
simple induction i; unfold AreIsos in |- *; intros f g p; elim p; auto.
Qed.

Lemma Inv_iso_unique :
 forall f g : Iso, Iso_mor f =_S Iso_mor g -> Inv_iso f =_S Inv_iso g.
Proof.
intros f g H.
apply Trans with ((Inv_iso f o Iso_mor f) o Inv_iso g).
apply Trans with (Inv_iso f o Iso_mor f o Inv_iso g).
apply Trans with (Inv_iso f o Id a).
apply Idr.
apply Comp_l.
apply Trans with (Iso_mor g o Inv_iso g).
apply Sym; apply (Idr_inv g).
apply Comp_r; apply Sym; trivial.
apply Ass.
apply Trans with (Id b o Inv_iso g).
apply Comp_r; apply (Idl_inv f).
apply Idl.
Qed.

Lemma RightInv_epic :
 forall (h : a --> b) (h1 : b --> a), RIso_law h h1 -> Epic_law h.
Proof.
intros h h1 H.
unfold Epic_law in |- *; intros c f g H1.
apply Trans with (Id b o f).
apply Idl1.
apply Trans with (Id b o g).
apply Trans with ((h1 o h) o f).
apply Comp_r; apply Sym; trivial.
apply Trans with ((h1 o h) o g).
apply Trans with (h1 o h o f).
apply Ass1.
apply Trans with (h1 o h o g).
apply Comp_l; trivial.
apply Ass.
apply Comp_r; trivial.
apply Idl.
Qed.

End iso_def.

Coercion RightInv_epic : RIso_law >-> Epic_law.

(* initial *)

Section initial_def.

Variable C : Category.

Definition IsInitial (a : C) (h : forall b : C, a --> b) :=
  forall (b : C) (f : a --> b), f =_S h b.
  
Structure > Initial : Type := 
  {Initial_ob : C;
   MorI : forall b : C, Initial_ob --> b;
   Prf_isInitial :> IsInitial MorI}.

Definition At_most_1mor (a b : C) := forall f g : a --> b, f =_S g.

Lemma UniqueI : forall (i : Initial) (b : C), At_most_1mor (Initial_ob i) b.
Proof.
intros i b; red in |- *; intros f g.
apply Trans with (MorI i b).
apply (Prf_isInitial (i:=i)).
apply Sym; apply (Prf_isInitial (i:=i)).
Qed.

Lemma I_unic : forall i1 i2 : Initial, Iso (Initial_ob i1) (Initial_ob i2).
Proof.
intros i1 i2.
apply
 (Build_Iso (Iso_mor:=MorI i1 (Initial_ob i2))
    (Inv_iso:=MorI i2 (Initial_ob i1))); unfold AreIsos in |- *;
 unfold RIso_law in |- *; split.
apply (UniqueI (i:=i2) (b:=Initial_ob i2)).
apply (UniqueI (i:=i1) (b:=Initial_ob i1)).
Defined.

End initial_def.

(* terminal *)

Section terminal_def.

Variable C : Category.

Definition IsTerminal (b : C) (h : forall a : C, a --> b) :=
  forall (a : C) (f : a --> b), f =_S h a. 

Structure > Terminal : Type := 
  {Terminal_ob : C;
   MorT : forall a : C, a --> Terminal_ob;
   Prf_isTerminal :> IsTerminal MorT}.

Lemma UniqueT : forall (t : Terminal) (a : C), At_most_1mor a (Terminal_ob t).
Proof.
intros t a; red in |- *; intros f g.
apply Trans with (MorT t a).
apply (Prf_isTerminal (t:=t)).
apply Sym; apply (Prf_isTerminal (t:=t)).
Qed.

End terminal_def.

Lemma Initial_dual :
 forall (C : Category) (a : C) (h : forall b : C, a --> b),
 IsInitial h -> IsTerminal (C:=Dual C) h.
Proof.
auto.
Qed.

Coercion Initial_dual : IsInitial >-> IsTerminal.

Definition IsTerminal' (C : Category) (b : C) (h : forall a : C, a --> b) :=
  IsInitial (C:=Dual C) h.
