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
(* generation of an ML File    *)
(*******************************)

Axiom int : Set. 
Axiom big_int : Set.
Axiom i2n : int -> nat. 
Axiom z2b : Z -> big_int. 

Extract Inlined Constant int => "int". 
Extract Constant big_int => "Big_int.big_int".

Extract Constant i2n =>
 "  
  let rec i2n = function 0 -> O | n -> (S (i2n (n-1)))
  in i2n
".


  Extract Constant z2b =>
   "
  let rec p2b = function 
     XH -> Big_int.unit_big_int
   | XO p -> Big_int.mult_int_big_int 2 (p2b p)
   | XI p -> Big_int.succ_big_int (Big_int.mult_int_big_int 2 (p2b p))
  in 
  function 
     Z0 -> Big_int.zero_big_int
   | Zpos p -> (p2b p)
   | Zneg p -> (Big_int.minus_big_int (p2b p))       
"
  .

  
Extract Inductive bool => bool [ true false ].
Extract Inductive sumbool => bool [ true false ].
Extract Inductive sigT => "(*)" [ "(,)" ].
  
Extraction Inline Wf_nat.gt_wf_rec Wf_nat.lt_wf_rec Wf_nat.induction_ltof2.

Extraction NoInline u o top pop.

Extraction NoInline M11 M12 M21 M22 Mat_mult.

Set Extraction AccessOpaque.

Extraction "fibo" fibonacci int big_int i2n z2b.
