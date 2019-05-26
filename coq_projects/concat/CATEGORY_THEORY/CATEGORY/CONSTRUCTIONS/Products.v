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
(*	                          Products              		     *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Category.
Require Export BasicTypes.

Set Implicit Arguments.
Unset Strict Implicit.

(* Products *)

Section prodts_def.

Variables (C : Category) (I : Type) (a : I -> C).

 Section prodts_laws.

 Variables (PI : C) (Proj : forall i : I, PI --> a i).

 Definition Product_eq (r : C) (h : forall i : I, r --> a i)
   (g : r --> PI) := forall i : I, h i =_S g o Proj i.

 Variable Pd_diese : forall r : C, (forall i : I, r --> a i) -> (r --> PI).

 Definition Product_law1 :=
   forall (r : C) (h : forall i : I, r --> a i), Product_eq h (Pd_diese h).

 Definition Product_law2 :=
   forall (r : C) (h : forall i : I, r --> a i) (g : r --> PI),
   Product_eq h g -> g =_S Pd_diese h.

 End prodts_laws.

Structure Product : Type := 
  {Pi : C;
   Proj : forall i : I, Pi --> a i;
   Pd_diese : forall r : C, (forall i : I, r --> a i) -> (r --> Pi);
   Prf_pd_law1 : Product_law1 Proj Pd_diese;
   Prf_pd_law2 : Product_law2 Proj Pd_diese}.

End prodts_def.

(* Binary Products *)

Section binprod'_def.

Variables (C : Category) (a b : C). 

Definition Fam2 (i : TwoElts) := match i with
                                 | Elt1 => a
                                 | Elt2 => b
                                 end.

Definition BinProd' := Product Fam2.

End binprod'_def.

