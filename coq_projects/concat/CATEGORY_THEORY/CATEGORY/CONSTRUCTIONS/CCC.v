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
(*	                Classical Definition of CCC                          *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Exponents.
Require Export CatProperty.

Set Implicit Arguments.
Unset Strict Implicit.

Structure IsCartesian (C : Category) : Type := 
  {Car_terminal :> Terminal C; Car_BP :> HasBinProd C}.

Structure Cartesian : Type := 
  {Car_Cat :> Category; Prf_isCartesian :> IsCartesian Car_Cat}.

Structure IsCCC (C : Category) : Type := 
  {CCC_isCar :> IsCartesian C; CCC_exponent :> HasExponent CCC_isCar}.

(* CCC Type *)

Structure CCC : Type :=  {CCC_Car :> Cartesian; Prf_isCCC :> IsCCC CCC_Car}.

(*
Variable C       : CCC.
Variable a, b, c : C.

Lemma Eq_CCC : (Iso (H_expo C a (H_obj_prod C b c)) (H_expo C (H_expo C a b) c)).
*)