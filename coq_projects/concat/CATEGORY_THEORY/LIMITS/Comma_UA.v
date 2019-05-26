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
(*	   A Universal Arrow is a Initial Object In Comma Category 	     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Comma.
Require Export UniversalArrow.

Set Implicit Arguments.
Unset Strict Implicit.

Section ua_comma.

Variables (A X : Category) (G : Functor A X) (x : X).

(* Un UA de x vers G est un obj initial dans (x|G) *)

Variable u : UA x G.

Canonical Structure UA_com_ob := Build_Com_ob (UA_mor u).

 Section ua_com_arrow_def.

 Variable axf : Comma G x.

 Lemma UA_com_law : Com_law (UA_diese u (Mor_com_ob axf)).
 Proof.
 unfold Com_law in |- *.
 elim axf; intros a f; simpl in |- *.
 apply UA_diag1.
 Qed.

 Canonical Structure UA_com_arrow := Build_Com_arrow UA_com_law.

 End ua_com_arrow_def.

Lemma UA_isInitial : IsInitial UA_com_arrow.
Proof.
unfold IsInitial in |- *; intros b f.
unfold UA_com_arrow in |- *; simpl in |- *; unfold Equal_com_arrow in |- *;
 simpl in |- *.
apply UA_unic.
apply Sym; apply (Prf_com_law f).
Qed.

Canonical Structure UA_Initial := Build_Initial UA_isInitial.

(* un obj initial dans (x|G) est Un UA de x vers G *)

Variable axu : Initial (Comma G x).

Definition Com_diese (a' : A) (f : x --> G a') :=
  Mor_com_arrow (MorI axu (Build_Com_ob f)).

Let axu_ob := Initial_ob axu.

Lemma Com_UAlaw1 : UA_law1 (Mor_com_ob axu_ob) Com_diese.
Proof.
unfold UA_law1, UA_eq in |- *; intros a' f.
apply Sym; exact (Prf_com_law (MorI axu (Build_Com_ob f))).
Qed.

Lemma Com_UAlaw2 : UA_law2 (Mor_com_ob axu_ob) Com_diese.
Proof.
unfold UA_law2, UA_eq in |- *; intros a' f g H.
cut (Com_law (bxg:=Build_Com_ob f) g).
intro H'.
apply (UniqueI (Build_Com_arrow H') (MorI axu (Build_Com_ob f))); auto.
unfold Com_law in |- *; simpl in |- *.
apply Sym; trivial.
Qed.

Lemma Com_isUA : IsUA (Mor_com_ob axu_ob).
Proof.
apply (Build_IsUA Com_UAlaw1 Com_UAlaw2).
Defined.
         
Canonical Structure Com_UA := Build_UA Com_isUA.

End ua_comma.
