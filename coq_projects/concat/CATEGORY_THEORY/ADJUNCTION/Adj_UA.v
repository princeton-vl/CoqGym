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
(*	            Relations between UA and Adjunctions      		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export CoUniversalArrow.
Require Export Adjunction.

Set Implicit Arguments.
Unset Strict Implicit.

(* extraction d'un UA et d'un coUA a` partir d'un adjonction *)

Section adj_to_ua.

Variables (C D : Category) (F : Functor D C) (G : Functor C D) (ad : Adj F G).
Variable d : D.

(* Prouver que pour tout d, <F(d),phi(Id(F(d)))> est UA de d vers G *)

Definition Unit_ob := F d.

Definition Unit_arrow := ApAphi ad (Id (F d)).
 
Definition Unit_arrow_diese (c : C) (f : d --> G c) := ApAphi_inv ad f.

(* qq c:C. qq f:d->Gc. f=phi<d,Fd>(Id(Fd)) o G(phi-1<d,c>(f)) (@) *)
(* remarquons que phi<d,c>(Id(Fd) o phi-1<d,c>(f)) = f *)
(* donc (@) est une instance de Adj_eq3 *)

Lemma Unit_UAlaw1 : UA_law1 Unit_arrow Unit_arrow_diese.
Proof.
unfold UA_law1, UA_eq, Unit_arrow_diese, Unit_arrow in |- *.
intros c1 f; apply Sym.
apply Trans with (ApAphi ad (Id (F d) o ApAphi_inv ad f)).
apply Trans with (ApAphi ad (ApAphi_inv ad f)).
apply Sym; exact (Idl_inv (NTa_areIso ad (Build_POb1 d c1)) f).
apply AphiPres; apply Idl1.
apply (Adj_eq3 ad (ApAphi_inv ad f) (Id (F d))).
Qed.

(* qq c1:C. qq f:d->Gc1. qq f':Fd->c1. *)
(* phi<d,Fd>(Id(Fd)) o G(f') = f (@) *)
(* => f'=phi-1<d,c1>(f) *)
(* appliquer phi-1<d,c1> aux 2 membres de (@) *)
(* En appliquant Adj_eq5, on obtient le re'sultat souhaite' *)

Lemma Unit_UAlaw2 : UA_law2 Unit_arrow Unit_arrow_diese.
Proof.
unfold UA_law2, UA_eq, Unit_arrow_diese, Unit_arrow in |- *.
intros c1 f f' H.
apply Trans with (ApAphi_inv ad (ApAphi ad (Id (F d)) o FMor G f')).
apply Sym.
apply Trans with (ApAphi_inv ad (ApAphi ad (Id (F d))) o f').
apply (Adj_eq5 ad f' (ApAphi ad (Id (F d)))).
apply Trans with (Id (F d) o f').
apply Comp_r; apply (Idr_inv (NTa_areIso ad (Build_POb1 d (F d))) (Id (F d))).
apply Idl.
apply Aphi_invPres; apply H.
Qed.

Canonical Structure Unit' := Build_IsUA Unit_UAlaw1 Unit_UAlaw2.

Canonical Structure Unit := Build_UA Unit'.

(* Prouver que pour tout c, <G(c),phi-1(Id(G(c)))> est UA de c vers F *)

Variable c : C.

Definition CoUnit_ob := G c.

Definition CoUnit_arrow := ApAphi_inv ad (Id (G c)).

Definition CoUnit_arrow_diese (d : D) (f : F d --> c) := ApAphi ad f.
                        
Lemma CoUnit_coUAlaw1 : CoUA_law1 CoUnit_arrow CoUnit_arrow_diese.
Proof.
unfold CoUA_law1, CoUA_eq, CoUnit_arrow_diese, CoUnit_arrow in |- *.
intros d1 f.
(* *) apply Trans with (ApAphi_inv ad (ApAphi ad f o Id (G c))).
apply Sym; apply (Adj_eq6 ad (ApAphi ad f) (Id (G c))).
(* *) apply Trans with (ApAphi_inv ad (ApAphi ad f)).
apply Aphi_invPres; apply Idr1.
apply (Idr_inv (NTa_areIso ad (Build_POb1 d1 c)) f).
Qed.

Lemma CoUnit_coUAlaw2 : CoUA_law2 CoUnit_arrow CoUnit_arrow_diese.
Proof.
unfold CoUA_law2, CoUA_eq, CoUnit_arrow_diese, CoUnit_arrow in |- *.
intros d1 f g H.
(* *) apply Trans with (ApAphi ad (FMor F g o ApAphi_inv ad (Id (G c)))).
(* *) apply Trans with (g o ApAphi ad (ApAphi_inv ad (Id (G c)))).
(* *) apply Trans with (g o Id (G c)).
apply Idr.
apply Comp_l; apply Sym.
apply (Idl_inv (NTa_areIso ad (Build_POb1 (G c) c)) (Id (G c))).
apply Sym; apply (Adj_eq4 ad g (ApAphi_inv ad (Id (G c)))).
apply AphiPres; apply H.
Qed.

Canonical Structure CoUnit' := Build_IsCoUA CoUnit_coUAlaw1 CoUnit_coUAlaw2.

Canonical Structure CoUnit := Build_CoUA CoUnit'.

End adj_to_ua.

