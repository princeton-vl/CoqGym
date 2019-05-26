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
(*	                      Equalizers                		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export CatProperty.

Set Implicit Arguments.
Unset Strict Implicit.

(* Equalizers *)

Section equaz_def.

Variables (C : Category) (a b : C) (I : Type) (k : I -> (a --> b)).

 Section equaz_laws.

 Variables (c : C) (e : c --> a).

 Definition Equalizer_eq (r : C) (h : r --> a) :=
   forall i j : I, h o k i =_S h o k j.

 Definition Equalizer_law1 := Equalizer_eq e.

 Variable E_diese : forall (r : C) (h : r --> a), Equalizer_eq h -> (r --> c).

 Definition Equalizer_law2 :=
   forall (r : C) (h : r --> a) (p : Equalizer_eq h), h =_S E_diese p o e.

 Definition Equalizer_law3 :=
   forall (r : C) (h : r --> a) (p : Equalizer_eq h) (l : r --> c),
   h =_S l o e -> l =_S E_diese p.

 End equaz_laws.

Structure Equalizer : Type := 
  {E_ob : C;
   E_mor : E_ob --> a;
   Prf_E_law1 : Equalizer_law1 E_mor;
   E_diese : forall (r : C) (h : r --> a), Equalizer_eq h -> (r --> E_ob);
   Prf_E_law2 : Equalizer_law2 E_mor E_diese;
   Prf_E_law3 : Equalizer_law3 E_mor E_diese}.

Variable f : Equalizer.

(* tout Equalizer est monic *)

Lemma E_monic : Monic_law (E_mor f).
Proof.
unfold Monic_law in |- *; intros c j l H.
cut (Equalizer_eq (j o E_mor f)).
intro p.
(* *) apply Trans with (E_diese f p).
apply (Prf_E_law3 p (l:=j)).
apply Refl.
apply Sym; apply (Prf_E_law3 p (l:=l)).
apply H.
unfold Equalizer_eq in |- *; intros i1 i2.
(* *) apply Trans with (j o E_mor f o k i1).
apply Ass1.
(* *) apply Trans with (j o E_mor f o k i2).
apply Comp_l; apply (Prf_E_law1 f i1 i2).
apply Ass.
Qed.

(* un epic Equalizer est iso *)

Lemma Epic_Equalizer_id : Epic_law (E_mor f) -> Equalizer_eq (Id a).
Proof.
unfold Equalizer_eq in |- *.
intros ep i1 i2.
(* *) apply Trans with (k i1).
apply Idl.
(* *) apply Trans with (k i2).
apply ep.
apply (Prf_E_law1 f i1 i2).
apply Sym; apply Idl.
Qed.

Lemma Epic_Equalizer_iso :
 forall p : Epic_law (E_mor f),
 let f1 := E_diese f (Epic_Equalizer_id p) in AreIsos (E_mor f) f1.
Proof.
intros p.
unfold AreIsos, RIso_law in |- *; split.
apply Sym; apply (Prf_E_law2 f (Epic_Equalizer_id p)).
apply E_monic.
(* *) apply Trans with (E_mor f o Id a).
(* *) apply Trans with (E_mor f o E_diese f (Epic_Equalizer_id p) o E_mor f).
apply Ass1.
apply Comp_l.
apply Sym; apply (Prf_E_law2 f (Epic_Equalizer_id p)).
(* *) apply Trans with (E_mor f).
apply Idr1.
apply Idl1.
Qed.

Lemma Equalizer_iso :
 forall (h1 : a --> E_ob f) (p : RIso_law (E_mor f) h1),
 let f1 := E_diese f (Epic_Equalizer_id (RightInv_epic p)) in
 AreIsos (E_mor f) f1.
Proof.
intros h1 ri; simpl in |- *; apply Epic_Equalizer_iso.
Qed.

End equaz_def.



