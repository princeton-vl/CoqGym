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


(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*                               Oct 1st 1996                               *)
(*                                                                          *)
(****************************************************************************)
(*                            MapProperty.v                                 *)
(*                            A. SAIBI (May 95)                             *)
(****************************************************************************)


Require Export Map.

Set Implicit Arguments.
Unset Strict Implicit.

(* Injective Map *)

Section inj_surj_def.

Variable A B : Setoid.

Definition Inj_law (f : Map A B) := forall x y : A, f x =_S f y -> x =_S y.

Structure > Inj : Type :=  {Inj_map :> Map A B; Prf_isInj :> Inj_law Inj_map}.

(* Surjective Map *)

Definition Surj_law (f : Map A B) (h : B -> A) := forall b : B, b =_S f (h b).

Structure > Surj : Type := 
  {Surj_map :> Map A B;
   Surj_elt : B -> A;
   Prf_isSurj :> Surj_law Surj_map Surj_elt}.

End inj_surj_def.



