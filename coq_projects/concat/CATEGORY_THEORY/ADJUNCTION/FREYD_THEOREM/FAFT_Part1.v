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
(*		                                 			     *)
(*	     The Special Adjoint Functor Theorem (Freyd's Theorem)	     *)
(*                      ( The necessary condition )                          *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Limit.
Require Export Adj_UA.
Require Export Single.
Require Export FAFT_SSC2.

Set Implicit Arguments.
Unset Strict Implicit.

(****************************************)
(* CONDITION NECESSAIRE                 *)
(****************************************)

Section freyd_th_1.

Variables (A X : Category) (G : Functor A X) (A_c : Complete A)
  (la : LeftAdj G).

Variable x : X.

Let I := UnitType.

Let a (i : I) := match i with
                 | Elt => Adjoint la x
                 end.

Let f (i : I) :=
  match i as i' return (Carrier (x --> G (a i'))) with
  | Elt => UA_mor (Unit la x)
  end.

 Section cd2.
 
 Variables (r : A) (h : x --> G r).
 
 Let i := Elt.

 Let t : a i --> r := ApAphi_inv la h.

 Lemma FT_cd2_law : h =_S f i o FMor G t.
 Proof.
 (* *) apply Trans with (ApAphi la (Id (Adjoint la x) o t)).
 (* *) apply Trans with (ApAphi la t).
 apply Sym.
 exact (Idl_inv (NTa_areIso la (Build_POb1 x r)) h).
 apply AphiPres.
 apply Idl1.
 apply (Adj_eq3 la t (Id (Adjoint la x))).
 Defined.

 Canonical Structure FT_cd2 := Build_Cond2 (I:=I) FT_cd2_law.
 
 End cd2.

Lemma AFT2 : SSC2 G x.
Proof.
exact (Build_SSC2 FT_cd2).
Qed.

End freyd_th_1.

