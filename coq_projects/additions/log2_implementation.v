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

(* -----                  log2_implementation.v                        ---- *)
(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(* 

This file contains an algorithm to compute the integer logarithm
 (base 2) of a given positive integer.
The  algorithm we give first  not only computes this
 logarithm, but returns also an information on it's exactness.

 Since we are interested in using Coq for low-levels programs,
 we choosed to realize  the specification of log2 with
 a while-loop using shift (multiplication by 2) and unshift
 (quotient by 2, and parity check).

*)

Require Import Arith.
Require Import Peano_dec.
Require Import Constants.
Require Import Mult_compl.
Require Import Wf_nat. 
Require Import euclid.
Require Import Le_lt_compl.
Require Import Euclid.
Require Import shift.
Require Import Compare_dec.
Require Import imperative.
Require Import while.
Require Import two_power.
Require Import log2_spec.


Section log2_computation.
 Variable n0 : nat.
 Hypothesis pos_n0 : 0 < n0.
 Hint Resolve pos_n0: arith.

 (* specification 
 *****************)
 (*
    It is easy, by a sequence of unshifts (right shifts) to
    compute, not only the integer logarithm (base 2 ) of a positive
    integer, but also to know  wether this logarithm is exact;
    the additionnal cost is a boolean variable, initialized with
    true, and set to false the first time a division by 2 returns a
    non null rest.
*)


 (*
  Sketch of the (imperative) program:
 
  n := n0;
  p:= O;
  b := true; /* n0=2^p * n  */

  while (n>O)  
  {
    if (b)  /* n0=2^p * n  */
      {
         if(n is even) 
            { p:=p+1;
              n:=unshift(n);
              b:=true}
         else
             {p:=p+1;
              n:=unshift(n);
              b:=false}
      }
     else   /* 2^p * n < n0 < 2^p(n+1) /\ n>0 */
      {
       p:=p+1;
       n:=unshift(n);
       b:=false}
    }
    return (p,b);
 *)

 
 
 (* computation states  
 **************************)
 
  Record state : Set := mkstate
    {state_n : nat; state_p : nat; state_b : bool}.
 
  Inductive ok : state -> Prop :=
    | oktrue : forall p : nat, n0 = two_power p -> ok (mkstate one p true)
    | okfalse :
        forall p : nat,
        two_power p < n0 -> n0 < two_power (S p) -> ok (mkstate one p false).

  Let init (s : state) := state_n s = n0 /\ state_p s = 0 /\ state_b s = true.





(* loop parameters *)
 (* exit predicate  (when to stop looping)
 ************************************************)
 
  Inductive final : state -> Prop :=
      mkfinal : forall (p : nat) (b : bool), final (mkstate one p b).
 
 (* loop invariant 
 *****************)
  (* in a state (mkstate n p b), the boolean b expresses
     the exactness of the logarithm to compute *)

  Inductive invar : state -> Prop :=
    | exact :
        forall n p : nat,
        n0 = two_power p * n -> 0 < n -> invar (mkstate n p true)
    | inexact :
        forall n p : nat,
        two_power p * n < n0 ->
        n0 < two_power p * S n -> 0 < n -> invar (mkstate n p false).
 
 
 (* termination order  (hope it's well founded !)
 ************************************************)
 
  Definition stat_order := ltof state state_n.
 
 
 (* technical lemmas 
  ******************)

 (* About states 
 ******************)

 (*Remark *) Lemma decomp :
              forall s : state,
              s = mkstate (state_n s) (state_p s) (state_b s).
 Proof.
   simple induction s; simpl in |- *; auto with arith.
 Qed.

 (* About the invariant 
 ***********************)



 (* Remark *) Lemma invar_inv1 :
               forall n p : nat,
               invar (mkstate n p true) -> n0 = two_power p * n.
 Proof.
  intros; inversion_clear H; auto with arith.
 Qed.

 (* Remark *) Lemma invar_inv2 :
               forall n p : nat,
               invar (mkstate n p false) ->
               two_power p * n < n0 /\ n0 < two_power p * S n.
 Proof.
  intros.
  inversion_clear H; split; auto with arith.
 Qed.

 (* Remark *) Lemma invar_inv3 :
               forall (n p : nat) (b : bool), invar (mkstate n p b) -> 0 < n.
 Proof.
  intros.
  inversion_clear H; auto with arith.
 Qed.


 (* About loop exiting 
 *********************)


 (* Remark *) Lemma final_inv :
               forall (n p : nat) (b : bool),
               final (mkstate n p b) -> n = one.
 Proof.
  intros.
  inversion_clear H; auto with arith.
 Qed.




 (* Remark *) Lemma not_final :
               forall (n p : nat) (b : bool),
               invar (mkstate n p b) -> ~ final (mkstate n p b) -> one < n.
 Proof.
  intros.
  case (le_or_lt n one); [ intro | auto with arith ].
  cut (0 < n); [ intro | apply invar_inv3 with p b; auto with arith ].
  case (enum1 n).
  unfold two in |- *; auto with arith.
  intro; absurd (0 < n); auto with arith.
  rewrite H3; auto with arith.
  intro; absurd (final (mkstate n p b)); [ auto with arith | idtac ].
  rewrite H3; split; auto with arith.
 Qed.



(* termination of the loop *)
(***************************)

 (* Remark *) Lemma wf_stat_order : well_founded stat_order.
 Proof.
  unfold stat_order in |- *; apply well_founded_ltof.
 Qed.
 Hint Resolve wf_stat_order: arith.

 Lemma log2_impl : log2_spec n0.
 (******************************)
 Proof.
  apply Imperative with state init ok;
   [ 
   (* :init *)
   exists (mkstate n0 0 true)
   | 
      (* :body *)
      intros a pre; apply while_not with init invar stat_order final a;
      [  
         (* :test *) 
         simple induction s; intros state_n0 state_p0 state_b0 i;
         elim (le_lt_eq_dec 1 state_n0); [ right | left | idtac ]
      | 
         (* :body *)
         simple induction s; intros state_n0 state_p0 state_b0; 
         elim state_b0; intros h i; elim (Unshift state_n0); 
         intros m b';
         [ elim b';
            [ exists (mkstate m (S state_p0) true)
            | exists (mkstate m (S state_p0) false) ]
         | exists (mkstate m (S state_p0) false) ]
      | idtac
      | idtac
      | idtac
      | idtac ]
   | 
      (* :return *)
      simple induction a; intros state_n0 state_p0 state_b0; 
      elim state_b0; intro h; exists state_p0 ].

(* :init *)
Hint Unfold init: arith.

split; auto; split; auto.

(* terminaison test : *)
red in |- *; intros f; inversion f; auto.
rewrite <- H0 in a0; simpl in a0.
absurd (1 < 1); auto with arith.
rewrite <- b; constructor 1.
inversion i; auto.

  (* one loop step: *)

  cut (one < state_n0).
  intro n_ge_1.
  2: apply not_final with state_p0 true; auto with arith.

  (*  b (state_b0) is true ,
   which means that until now all the quotients by 2 were exact,
   or more precisely:  *)

  inversion i.
  
  (* m is exactly the half of state_n0n *)
  (**************************************)  

  split.
  left.
  rewrite two_power_S.
  rewrite <- mult_assoc; auto with arith.
  unfold shift in a0.
  rewrite <- a0; auto.
  unfold shift in a0.
  apply quotient_positive with state_n0 two; auto.
  rewrite mult_comm; exact a0.
  unfold stat_order, ltof in |- *.
  apply half_lt.
  apply lt_trans with one; auto with arith.
  auto with arith.

  (* state_n0=S(shift m) *)
  (***********************)

  cut (one < state_n0).
  intro n_ge_1.
  2: apply not_final with state_p0 true; auto with arith.
  inversion i.

  split.
  right.
  rewrite two_power_S.
  rewrite <- mult_assoc; auto with arith.
  rewrite (invar_inv1 state_n0 state_p0); auto.
  rewrite b.
  unfold shift in |- *.
  auto with arith.
  rewrite two_power_S.
  rewrite <- mult_assoc.
  rewrite (invar_inv1 state_n0 state_p0); auto.
  rewrite b.
  unfold shift in |- *.
  apply mult_lt_l.
  auto with arith.
  simpl in |- *; auto with arith.
  case (lt_or_Zero m); auto with arith.
  intro.
  absurd (one < state_n0); auto with arith.
  rewrite b.
  rewrite H3; simpl in |- *; auto with arith.
  unfold stat_order, ltof in |- *; apply half_lt.
  simpl in |- *.
  apply lt_trans with one; auto with arith.
  auto with arith.

 (* b (state_b0) is false , and will be false for ever,
     the logarithm will be inexact; the situation is 
     expressed by the four following cuts
  *)

  cut (one < state_n0).
  intro n_ge_1.
  2: apply not_final with state_p0 false; auto with arith.
  inversion i.

  cut (two_power (S state_p0) * m < n0).
  intro n0_left'.

  cut (n0 < two_power (S state_p0) * S m).
  intro n0_right'.

  cut (m < state_n0).
  intro m_little.

  split.
  right; auto with arith.
  case (lt_or_Zero m); auto with arith.
  intro.
  absurd (one < state_n0); auto with arith.
  simpl in b'; elim b'; intros eg; rewrite eg.
  rewrite H4; simpl in |- *; auto with arith.
  rewrite H4; simpl in |- *; auto with arith.
  unfold stat_order, ltof in |- *.
  simpl in |- *.
  exact m_little.
 

  (* proof of m_little (last cut) *)

  apply half_lt.
  apply lt_trans with one; auto with arith.
  simpl in b'; elim b'; auto with arith.

 (* Proof of n0_right':
     (lt n0 (mult (two_power (S state_p0)) (S m))). *)

  simpl in b'; elim b'; intros eg.
  apply lt_trans with (two_power state_p0 * S state_n0); auto with arith.
  rewrite two_power_S.
  rewrite <- mult_assoc; auto with arith.
  apply mult_lt_l.
  auto with arith.
  rewrite eg.
  unfold shift in |- *; simpl in |- *; auto with arith.
  replace (two_power (S state_p0) * S m) with
   (two_power state_p0 * S state_n0).
  elim (invar_inv2 state_n0 state_p0); auto with arith.
  elim H0; auto with arith.
  rewrite two_power_S.
  rewrite <- mult_assoc.
  simpl in |- *.
  unfold shift in |- *; simpl in |- *.
  rewrite <- plus_n_Sm.
  rewrite eg; auto with arith.

 (* proof of n0_left':(lt (mult (two_power (S state_p0)) m) n0). *)

  apply le_lt_trans with (two_power state_p0 * state_n0); auto with arith.
  simpl in b'; elim b'; intro eg.
  rewrite eg.
  rewrite two_power_S.
  rewrite <- mult_assoc; auto with arith.
  rewrite eg.
  rewrite two_power_S.
  rewrite <- mult_assoc; auto with arith.

  (* (s:state)(final s)->(invar s)->(ok s) *)
  simple induction s.
  simple induction state_b0.
  intros.
  rewrite (final_inv state_n0 state_p0 true).
  
  left.
  rewrite (invar_inv1 _ _ H0).
  rewrite (final_inv _ _ _ H).
  auto with arith.
  auto with arith.
  
  intros.
  rewrite (final_inv state_n0 state_p0 false).
  right.
  (* (lt (two_power state_p0) n0) *)
  elim (invar_inv2 _ _ H0).
  rewrite (final_inv _ _ _ H).
  intros.
  rewrite <- (mult_1_r (two_power state_p0)); auto with arith.
  (*  (lt n0 (two_power (S state_p0))) *)
  
  elim (invar_inv2 _ _ H0).
  rewrite (final_inv _ _ _ H).
  intros.
  rewrite two_power_S.
  exact H2.
  auto with arith.
  
  (*  (s:state)(init s)->(invar s) *)
  simple induction s.
  simple induction state_b0.
  intro.
  inversion_clear H.
  elim H1.
  simpl in |- *; intros.
  left.
  rewrite H; simpl in |- *.
  rewrite <- H0; auto with arith.
  simpl in H0; rewrite H0; auto with arith.
  
  intro.
  inversion_clear H.
  elim H1.
  intros.
  simpl in H2.
  discriminate H2.
  
  
  auto with arith.
  auto with arith.
  (* exit *)
			 
  left.
  inversion h; auto.
 
  right.
  inversion h; split; auto.


Qed. 

End log2_computation.
