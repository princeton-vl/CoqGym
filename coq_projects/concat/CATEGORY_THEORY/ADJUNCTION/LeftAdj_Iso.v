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
(*                   Two Left Adjoints of a Functor are Iso                  *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Adjunction1.

Set Implicit Arguments.
Unset Strict Implicit.

Section ladj_iso_def.

Variables (C D : Category) (G : Functor C D) (la la' : LeftAdj G).

Let F := Adjoint la.

Let F' := Adjoint la'.

Let LAdj_unit (a : D) := Unit la a. 

Let LAdj_unit' (a : D) := Unit la' a. 

Definition LAdj_tau_iso (a : D) := UA_iso (LAdj_unit a) (LAdj_unit' a).

Definition LAdj_tau (a : D) := Iso_mor (LAdj_tau_iso a).

Lemma LAdj_nt_law : NT_law LAdj_tau.
Proof.
unfold NT_law in |- *; intros a b f.
apply Trans with (UA_diese (LAdj_unit a) (f o UA_mor (LAdj_unit' b))).
apply (UA_unic (u:=LAdj_unit a)).
apply
 Trans
  with ((UA_mor (LAdj_unit a) o FMor G (FMor F f)) o FMor G (LAdj_tau b)).
apply
 Trans with (UA_mor (LAdj_unit a) o FMor G (FMor F f) o FMor G (LAdj_tau b)).
apply Comp_l; apply FComp.
apply Ass.
apply Trans with ((f o UA_mor (LAdj_unit b)) o FMor G (LAdj_tau b)).
apply Comp_r; apply Sym; apply (Prf_NT_law (Unit_NT la) f).
apply Trans with (f o UA_mor (LAdj_unit b) o FMor G (LAdj_tau b)).
apply Ass1.
apply Comp_l; apply (UA_diag (LAdj_unit b) (UA_mor (LAdj_unit' b))).
apply (UA_unic1 (u:=LAdj_unit a)).
apply
 Trans with (UA_mor (LAdj_unit a) o FMor G (LAdj_tau a) o FMor G (FMor F' f)).
apply Comp_l; apply FComp.
apply
 Trans
  with ((UA_mor (LAdj_unit a) o FMor G (LAdj_tau a)) o FMor G (FMor F' f)).
apply Ass.
apply Trans with (UA_mor (LAdj_unit' a) o FMor G (FMor F' f)).
apply Comp_r; apply (UA_diag (LAdj_unit a) (UA_mor (LAdj_unit' a))).
apply Sym; apply (Prf_NT_law (Unit_NT la') f).
Qed.

Canonical Structure LAdj_nt := Build_NT LAdj_nt_law.

Lemma LAdj_iso : NatIso F F'.
Proof.
apply (NT_Iso (T:=LAdj_nt) (h:=fun a : D => Inv_iso (LAdj_tau_iso a))).
intro a; exact (UA_iso_law1 (LAdj_unit a) (LAdj_unit' a)).
Qed.

End ladj_iso_def.