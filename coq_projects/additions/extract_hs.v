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



Require Import Constants.
Require Import generation.
Require Import monoid.
Require Import machine.
Require Import strategies.
Require Import spec.
Require Import log2_spec.
Require Import log2_implementation.
Require Import Compare_dec.
Require Extraction.

Require Import while.
Require Import imperative.
Require Import develop.
Require Import dicho_strat.
Require Import binary_strat.
Require Import trivial.
Require Import standard.
Require Import monofun.
Require Import matrix.
Require Import ZArith.
Require Import main.

(*******************************)
(* generation of an Haskell File *)
(*******************************)

Extraction Language Haskell.

Axiom int : Set. 
Axiom i2n : int -> nat. 
Axiom z2i : Z -> int. 

Extract Inlined Constant int => "Integer". 

Extract Constant i2n =>
 "\n -> 
   case n of  
     0 -> O
     n -> S (i2n (n-1))  
".


Extract Constant z2i =>
   "
  let p2b XH = 1
      p2b (XO p) = 2*(p2b p)
      p2b (XI p) = 2*(p2b p)+1
  in 
  \z -> case z of 
          Z0 -> 0
          Zpos p -> (p2b p)
          Zneg p -> - (p2b p)
".

Extract Inductive bool => Bool [ True False ].
Extract Inductive sumbool => Bool [ True False ].
	    
Extraction Inline Wf_nat.gt_wf_rec Wf_nat.lt_wf_rec induction_ltof2.

Extraction NoInline u o top pop.

Extraction NoInline M11 M12 M21 M22 Mat_mult.

Set Extraction AccessOpaque.

Extraction "Fibo" fibonacci int i2n z2i.

(* finally, 
     import qualified Prelude 
   is to be replaced by 
     import Prelude
*)
