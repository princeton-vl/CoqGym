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
(* generation of an Scheme File *)
(*******************************)

Extraction Language Scheme.

Axiom int : Set. 
Axiom i2n : int -> nat. 
Axiom z2i : Z -> int. 

Extract Inlined Constant int => "int". 

Extract Constant i2n =>
 "(lambda (i) (if (zero? i) `(O) `(S ,(i2n (- i 1)))))".

Extract Constant z2i =>
 "(lambda (z)
    (define (p2i p)
      (match p
        ((XH) 1)
        ((XO p) (* 2 (p2i p)))
        ((XI p) (+ 1 (* 2 (p2i p))))))
    (match z
       ((Z0) 0)
       ((Zpos p) (p2i p))
       ((Zneg p) (- (p2i p)))))
  ".

Extraction Inline Wf_nat.gt_wf_rec Wf_nat.lt_wf_rec.

Extraction NoInline u o top pop.

Extraction NoInline M11 M12 M21 M22 Mat_mult.

Set Extraction AccessOpaque.

Extraction "fibo" fibonacci i2n z2i.

(* After fetching macro_extr.scm (see header of fibo.scm),
   a typical session would look like: 
  
    (load "fibo.scm")
    (z2i (fibonacci (i2n 100)))

*)
