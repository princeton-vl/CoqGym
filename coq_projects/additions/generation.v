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


(* ----                 generation.v ----                                   *)

(*                                                                          *)
(* Author: Pierre Casteran.                                                 *)
(*    LABRI, URA CNRS 1304,                                                 *)
(*    Departement d'Informatique, Universite Bordeaux I,                    *)
(*    33405 Talence CEDEX,                                                  *)
(*    e-mail:  casteran@labri.u-bordeaux.fr                                 *)

(*

  This file uses the results of "develop" to validate the chain 
  generation algorithm; see also the "spec" module.

*)
  
Require Import monoid.
Require Import spec.
Require Import Constants.
Require Import machine.
Require Import Euclid.
Require Import Le_lt_compl.
Require Import euclid.
Require Import shift.
Require Import two_power.
Require Import log2_spec.
Require Import develop.
Require Import Arith.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import strategies.
Require Import Mult_compl.
Require Import Wf_nat.
Require Import Wf_compl.


(* termination of the addition chain algorithm *)
(***********************************************)

(* termination order (based on recursive calls) *)

Inductive Call_lt : Call -> Call -> Prop :=
  | M_M_lt : forall p q : nat, p < q -> Call_lt (Call_M p) (Call_M q)
  | C_M_lt : forall p q : nat, p < q -> Call_lt (Call_C q p) (Call_M q)
  | M_C_lt : forall p q r : nat, p < r -> Call_lt (Call_M p) (Call_C r q)
  | M_K_lt : forall p q r : nat, p <= r -> Call_lt (Call_M p) (Call_K r q)
  | K_C_lt : forall p q r s : nat, q < s -> Call_lt (Call_K q p) (Call_C s r)
  | K_K_lt : forall p q r s : nat, q < s -> Call_lt (Call_K q p) (Call_K s r).

(* In order to prove well-foundedness of Call_lt, we use an
   auxiliary ad-hoc measure *)


Definition Call_measure (c : Call) :=
  match c return nat with
  | Call_M n =>
      (* Call_M n *)
      S (three * n)
      (* Call_C n p *)
  | Call_C n p => three * n
      (* Call_K n p *)
  | Call_K n p => S (S (three * n))
  end.


Lemma measure_compat : coarser Call Call_lt (ltof Call Call_measure).
(**************************************************)
Proof.
 unfold coarser, ltof in |- *.
 simple induction 1; unfold Call_measure in |- *. 
 intros; apply lt_n_S; apply mult_lt_l; auto with arith.
 unfold three in |- *; auto with arith.
 auto with arith.
 intros.
 apply lt_le_trans with (three * S p).
 simpl in |- *.
 apply lt_n_S.
 rewrite <- plus_n_O.
 apply plus_lt_compat_l.
 rewrite <- plus_Snm_nSm.
 simpl in |- *; auto with arith.
 auto with arith.
 auto with arith.
 intros.
 apply lt_le_trans with (three * S q).
 replace (three * S q) with (S (S (S (three * q)))).
 auto with arith.
 rewrite <- mult_n_Sm.
 rewrite plus_comm; simpl in |- *; auto with arith.
 auto with arith.
 intros; do 2 apply lt_n_S; apply mult_lt_l; auto with arith.
 unfold three in |- *; auto with arith.
Qed.



Lemma Wf_Call_lt : well_founded Call_lt.
(********************************************)
Proof.
 apply wf_coarser with (ltof Call Call_measure).
 exact measure_compat.
 apply well_founded_ltof.
Qed.



(* code generation algorithm *)
(*****************************)

Section generation.
  Variable gamma : strategy.
  Variable log2_r : forall n : nat, 0 < n -> log2_spec n.

  (* treatment of the 3 cases for (Call_M p)
       - p = 3
       - p is a power of 2 (q is the exponent)
       - we use (gamma p) as an intermediate value
  *)
             

  Lemma chain_cases :
   forall p : nat,
   0 < p ->
   {q : nat | q < p /\ two <= q} + {l : nat | p = two_power l} + {p = three}.
  (*******************************************************)
  Proof.
  refine
   (fun p _H =>
    match eq_nat_dec p three with
    | left h => inright _ h
    | right n =>
        match log2_r p _ with
        | existS l b =>
            match b with
            | left _ => inleft _ (inr _ (exist _ l _))
            | right a =>
                match gamma with
                | mkstrat s =>
                    match s p _ with
                    | exist q _ => inleft _ (inl _ (exist _ q _))
                    end
                end
            end
        end
    end); auto.
(*
  Realizer [p:nat]<sumor (sum nat nat)>if (eq_nat_dec p three)
                  then (inright (sum nat nat))
                  else <(sumor (sum nat nat))> 
                    let (l:nat;b:bool)=(log2_r p) in
                    <(sumor (sum nat nat))>if b 
                                           then
                                             (inleft
                                                 (sum nat nat)
                                                 (inr nat nat l))
                                           else (inleft (sum nat nat)
                                                 (inl nat nat
                                                      (gamma p))).
  Program_all.
*)
  case (le_or_lt (S four) p); [ auto with arith | intro H2 ].
  case (enum4 p H2); intro.
  absurd (0 < p); [ rewrite H; auto with arith | auto with arith ]. 
  elim H; intro H3.
  absurd (p = one); [ replace one with (two_power 0) | auto with arith ].
  apply holes_in_powers with l; elim a; auto with arith.
  simpl in |- *; auto with arith.
  elim H3; intro H4.  
  absurd (p = two); [ replace two with (two_power one) | auto with arith ].
  apply holes_in_powers with l; elim a; auto with arith.
  simpl in |- *; auto with arith. 
  elim H4; intro H5.
  elim (n H5).
  absurd (p = four); [ replace four with (two_power two) | auto with arith ].
  apply holes_in_powers with l; elim a; auto with arith.
  simpl in |- *; auto with arith. 
 Qed.


(* rougly speaking, COND3 can be used as a specialized control
   structure:
   In Real programs,
   (Cond3 A p case3
              case_2q
              case_gamma)
   is equivalent to :
  "if p = 3 
   then case3
   else if p is the q_th power of 2, 
        then (case_2q q)
        else (case_gamma (gamma p))"
*)


 Lemma COND3 :
  forall (A : nat -> Set) (p : nat),
  (p = three -> A p) ->
  (forall q : nat, p = two_power q -> A p) ->
  (forall q : nat, q < p -> two <= q -> A p) -> 0 < p -> A p.
(*********************************************)
 Proof.
 refine
  (fun A p case3 case_2n case_gamma h =>
   match chain_cases p _ with
   | inleft b =>
       match b with
       | inl b1 => match b1 with
                   | exist q hq => case_gamma q _ _
                   end
       | inr b2 => match b2 with
                   | exist q hq => case_2n q hq
                   end
       end
   | inright h => case3 h
   end); auto; elim hq; auto.
(*
  Realizer [A:Set][p:nat]
                 [case3:A]
                 [case_2n:nat->A]
                 [case_gamma:nat->A]
                 <A>Match (chain_cases p) with
                    [b:(sum nat nat)]
                        <A >Match b with
                            [q:nat](case_gamma q)
                            [q:nat](case_2n q) end
                    case3  end.
  Program_all.
  Elim a;Auto with arith.
  Elim a;Auto with arith.
*)
 Qed.


 (* the code generation algorithm  *)
 (* the labels A,B,C,A1,A2,A3,B1,B2,C1,C2, in the proof comments
    correspond to the following places in the program:

     Match c with
       A: (Call_M p)
         (COND3 
           A1: (p=3) ...
           A2: (p=2^q) ...
           A3: (q=gamma(p)) ...)
       B: (Call_C n n0)
           ... if (zerop r)
               then B1: ...
               else B2: ...

       C: (Call_K n n0)
           ... if (zerop r)
               then C1: ...
               else C2: ...
     end.
*)

    
 Lemma chain_algo : forall c : Call, conform c -> gencode c.
 (******************************************)
 Proof.
 refine
  (well_founded_induction Wf_Call_lt (fun c => conform c -> gencode c) _).
 intros c; case c; [ intro p | intros p n0 | intros p n0 ]; intros hr hc;
  simpl in hc.

 apply (COND3 (fun n => gencode (Call_M n)) p); auto with arith.
 intros h; rewrite h; apply M3.
 intros q h; rewrite h; apply M2q.
 refine (fun q _ _ => C2M p q (hr (Call_C p q) _ _)); auto with arith.
  constructor 2; auto with arith.
  simpl in |- *; auto with arith.

 elim hc; intros hc1 hc2.
 cut (n0 > 0);
  [ intro Hn0 | unfold gt in |- *; apply lt_trans with 1; auto with arith ].
 elim (eucl_dev n0 Hn0 p); intros q r E1 E2.
 elim (zerop r); intro Z.
 rewrite Z in E2; rewrite <- plus_n_O in E2; rewrite E2.
 cut (0 < q).
 intro Hq.
 refine (MMC n0 q (hr (Call_M n0) _ _) (hr (Call_M q) _ _)).
  constructor 3; auto with arith.
  simpl in |- *; auto with arith.
  constructor 3.
  rewrite E2; rewrite <- mult_comm; apply mult_p_lt_qp; auto with arith.
  simpl in |- *; auto with arith.
 
  apply quotient_positive with p n0; auto with arith.
  apply le_lt_trans with n0; auto with arith.

 cut (0 < q).
 intro Hq; rewrite E2.
 refine (KMC n0 q r (hr (Call_K n0 r) _ _) (hr (Call_M q) _ _)).
  constructor 5; auto with arith.
  simpl in |- *; auto with arith.
  constructor 3; auto with arith.
  rewrite E2; auto with arith.  
  simpl in |- *; auto with arith.

  apply lt_O_q with n0 r; auto; rewrite <- E2; auto.

 elim hc; intros hc1 hc2.
 cut (n0 > 0); [ intro Hn0 | unfold gt in |- *; auto with arith ].
 elim (eucl_dev n0 Hn0 p); intros q r E1 E2.
 elim (zerop r); intro Z.
 rewrite Z in E2; rewrite <- plus_n_O in E2; rewrite E2.
 cut (0 < q).
 intro Hq.
 refine (MMK n0 q (hr (Call_M n0) _ _) (hr (Call_M q) _ _)).
  constructor 4; auto with arith.
  simpl in |- *; auto with arith.
  constructor 4.
  rewrite E2; apply mult_p_le_pq; auto with arith.
  simpl in |- *; auto with arith.
 
  apply quotient_positive with p n0; auto with arith.
  apply le_lt_trans with n0; auto with arith.

 cut (0 < q).
 intro Hq; rewrite E2.
 refine (KMK n0 q r (hr (Call_K n0 r) _ _) (hr (Call_M q) _ _)). 
  constructor 6; auto with arith.
  simpl in |- *; auto with arith.
  constructor 4; auto with arith.
  rewrite E2; auto with arith.  
  simpl in |- *; auto with arith.

  apply lt_O_q with n0 r; auto; rewrite <- E2; auto.

Qed.

 Lemma power_algo : forall n : nat, 0 < n -> addchain_spec n.
 (***************************************************)
 Proof.
  intros; split.
  apply chain_algo.
  simpl in |- *; auto with arith.
 Qed.
 

End generation.





















