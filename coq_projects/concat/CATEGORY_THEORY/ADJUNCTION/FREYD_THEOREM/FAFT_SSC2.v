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
(*                      ( The Solution Set Condition )                       *)
(*									     *)
(*****************************************************************************)
(*									     *)
(*                     A. SAIBI	  May 95                  		     *)
(*									     *)
(*****************************************************************************)

Require Export Functor.

Set Implicit Arguments.
Unset Strict Implicit.

(**************************)
(* Solution Set Condition *)
(**************************)

Section ssc2_def.

Variables (A X : Category) (G : Functor A X) (x : X).

Structure Cond2 (I : Type) (l : I -> A) (f : forall i : I, x --> G (l i))
  (a : A) (h : x --> G a) : Type := 
  {Cond2_i : I;
   Cond2_t : l Cond2_i --> a;
   Prf_Cond2_law : h =_S f Cond2_i o FMor G Cond2_t}.

Structure SSC2 : Type := 
  {SSC2_I : Type;
   SSC2_a : SSC2_I -> A;
   SSC2_f : forall i : SSC2_I, x --> G (SSC2_a i);
   SSC2_p : forall (a : A) (h : x --> G a), Cond2 SSC2_f h}.

Variables (s : SSC2) (a : A) (h : x --> G a).

Definition SSC2_i := Cond2_i (SSC2_p s h).

Definition SSC2_t := Cond2_t (SSC2_p s h).

Lemma Prf_SSC2_law : h =_S SSC2_f SSC2_i o FMor G SSC2_t.
Proof.
exact (Prf_Cond2_law (SSC2_p s h)).
Qed.

End ssc2_def.
