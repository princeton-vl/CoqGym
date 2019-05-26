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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(*  ---                       dicho_strat.v                    --- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)


(*

 This file presents our favorite strategy, which gave the best results 
 (see the included paper)

 Briefly:


 dicho-strat(n)=
     let l=(ceiling_log2 log2 n)
     in (eucl_dev (two_power (eucl_dev 2 l)) n)
  
  (recall that in the distribution (quotient b a) is the notation
   for the euclidean division of a by b !)

 For instance let n be 87,
 The ceiling logarithm (base 2) of n is l=7 since 64<n<=128 ;
 thus the quotient of 87 by 2^3 is 10.

 Perhaps it's easier to understand this strategy in terms of
binary representation of natural integers:

 For instance, 87 is represented by 1010111; if we cut this
representation in two halves (the shorter at the right hand side,
if the number of digits is odd), we have two words:
   -   1011 -> 10 (it is just dicho_strat(10))
   -    111 -> 7
 Since we have 87=8*10+7,
 the code for (CALL_M 87) will be the  code for (CALL_C 87 10),
 i.e. the concatenation of the code for (CALL_K 10 7), 
 the code for (CALL_M 8), and a MUL statement:
   
    Statement  register  stack

 code for (CALL_K 10 7):

                x         []     
    PUSH        x         [x]
    PUSH        x         [x,x]
    SQR         x^2       [x,x]
    MUL         x^3       [x]
    PUSH        x^3       [x^3,x]
    SWAP        x^3       [x,x^3]
    SQR         x^6       [x,x^3]
    MUL         x^7       [x^3]
    PUSH        x^7       [x^7,x^3]
    SWAP        x^7       [x^3,x^7]
    MUL         x^10      [x^7]
    
 code for (CALL_M 8):

    SQR         x^20      [x^7]
    SQR         x^40      [x^7]
    SQR         x^80      [x^7]

 the final MUL:
    MUL         x^87      []


  The proof is very long, and we hope to shorten it
  quickly.


*)

Require Import strategies.
Require Import Arith.
Require Import euclid.
Require Import shift.
Require Import two_power.
Require Import log2_spec.
Require Import Euclid.
Require Import Le_lt_compl.
Require Import Mult_compl.
Require Import Constants.

Section import_log2.
Variable log2_r : forall n : nat, 0 < n -> log2_spec n. 

Lemma dicho : strategy.
(*******************)
Proof.
 split.
 intros n H.
 elim (ceiling_log2 log2_r n).
 2: apply lt_trans with four; unfold one, four in |- *; auto with arith.
 intros x y.
 elim y; intros.
 cut (0 < 2).
 2: auto with arith.
 intro H'.
 elim (quotient 2 H' x); intros.
 refine match quotient (two_power x0) _ n with
        | exist n0 e => exist _ n0 _
        end.

 unfold gt in |- *.
 apply lt_le_trans with 1; auto with arith.

 elim p; intros.
 elim e; intros.
 elim H2; intros H4 H5.
 elim H3; intros H6 H7.
 clear y p e H2 H3 H'.
 cut (0 < x0).
 2: case (lt_or_Zero x0); [ auto with arith | intro ].
 2: cut (x <= one).
 2: intro.
 2: absurd (n <= two).  
 2: unfold not in |- *; intro.
 2: absurd (four < two).  
 2: apply le_not_lt; auto with arith.
 2: unfold four, two in |- *; auto with arith.
 2: apply lt_le_trans with n; auto with arith.
 2: replace two with (two_power one).
 2: apply le_trans with (two_power x).
 2: auto with arith.
 2: apply two_power_le; auto with arith.
 2: simpl in |- *; auto with arith.
 2: rewrite H4; rewrite H2; simpl in |- *; auto with arith.
 intro x0_pos.
 cut (1 < two_power x0).
 2: replace 1 with (two_power 0).
 2: apply two_power_mono; auto with arith.
 2: simpl in |- *; auto with arith.
 intro H8. (* (lt (S O) (two_power x0) *)
 cut (x0 < x).
 2: rewrite H4.
 2: apply lt_le_trans with (x0 * 2).
 2: rewrite mult_comm; apply mult_p_lt_qp; auto with arith.
 2: auto with arith.
 intro H9.
 cut (x0 <= pred x).
 2: apply le_S_n.
 2: elim (S_pred _ _ H9).
 2: auto with arith.
 intro H10.
 cut (0 < n0).
 2: case (lt_or_Zero n0); [ auto with arith | intro ].
 2: absurd (n < two_power x0).
 2: apply le_not_lt.
 2: apply le_trans with (two_power (pred x)).
 2: apply two_power_le; auto with arith.
 2: auto with arith.
 2: rewrite H6; rewrite H2; simpl in |- *.
 2: auto with arith.
 intro H11. (* lt O n0 *)
 split.
 apply lt_le_trans with (n0 * two_power x0).
 rewrite mult_comm; apply mult_p_lt_qp; auto with arith.
 rewrite H6; auto with arith.

 apply not_lt_le.
 unfold not in |- *; intro H12.
 case (enum1 n0 H12); intro.
 absurd (0 < n0); [ rewrite H2; auto with arith | auto with arith ].

 cut (n < two_power (S x0)).
 2: rewrite H6.
 2: rewrite H2.
 2: rewrite mult_1_l.
 2: rewrite two_power_S.
 2: rewrite mult_comm; simpl in |- *.
 2: rewrite <- plus_n_O.
 2: apply plus_lt_compat_l.
 2: auto with arith.
 intro.
 cut (two_power x0 <= n).
 intro H13.
 cut (S x0 <= x); [ intro H14 | auto with arith ].
 case (le_lt_or_eq _ _ H14); intro.
 cut (S x0 <= pred x); [ intro | auto with arith ].
 absurd (n < n); [ auto with arith | idtac ].
 apply lt_trans with (two_power (S x0)).
 auto with arith.
 apply le_lt_trans with (two_power (pred x)).
 apply two_power_le; auto with arith.
 auto with arith.
 
 cut (x0 <= 1).
 intro H16.
 absurd (n < four).
 apply lt_asym.
 auto with arith.

 apply lt_le_trans with (two_power (S x0)).
 auto with arith.
 replace four with (two_power 2).
 apply two_power_le; auto with arith.
 unfold four in |- *; simpl in |- *; auto with arith.
 apply (fun p n m : nat => plus_le_reg_l n m p) with x0.
 replace (x0 + x0) with (x0 * 2).
 rewrite plus_comm; simpl in |- *.
 apply le_trans with x.
 rewrite H4; auto with arith.
 elim H15; auto with arith.
 rewrite mult_comm; simpl in |- *; rewrite <- plus_n_O; auto with arith.
 rewrite <- (mult_1_l (two_power x0)).
 elim H2; rewrite H6; auto with arith.
Qed.

End import_log2.


