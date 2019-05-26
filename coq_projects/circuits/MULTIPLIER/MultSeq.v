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

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: july 1995                                              *)
(* file: MultSeq.v                                              *)
(* contents: VERIFICATION OF A SEQUENTIAL MULTIPLIER.           *)
(* Proofs of the invariant and the final theorem                *)
(****************************************************************)

Require Import Definitions.
Require Import LemPrelim.
Require Import AdderProof.


(* L'invariant est :
si t<= size alors nat(R1(t)[size-t:size-1]@R2(t))=nat(V2)*nat(V1[0:t-1])
*)

(****************************************************************)
(* D'abord on prouve l'invariant pour t=O: *)

Lemma Invariant_t_O :
 BV_to_nat (appbv (stripbv (R1 0) size) (R2 0)) =
 BV_to_nat V2 * BV_to_nat (truncbv V1 0).
intros. simpl in |- *.
rewrite BV_to_nat_app2. rewrite (trunc_O bool). rewrite <- length_V1_size.
rewrite (strip_all bool). rewrite length_V1_size.
simpl in |- *. elim plus_n_O. elim mult_n_O. rewrite BV_null_nat. trivial with arith.
Qed.

(****************************************************************)
(* Ensuite, lors de la preuve par induction pour t quelconque,
   on doit faire une preuve par cas selon R1[0].
   On fait la preuve pour R1[0]=false:  (assez long)
*)

Lemma inv_ind_false :
 forall t n : nat,
 (n <= size ->
  BV_to_nat (appbv (stripbv (R1 n) (size - n)) (R2 n)) =
  BV_to_nat V2 * BV_to_nat (truncbv V1 n)) ->
 S n <= size ->
 n <= size ->
 BV_to_nat
   (appbv
      (stripbv
         (appbv (highs (R1 n))
            (Mux false (abit (BV_full_adder_sum (R2 n) V2 false) 0)
               (consbv (lowbit (R2 n)) nilbv))) (size - S n))
      (appbv (highs (Mux false (BV_full_adder_sum (R2 n) V2 false) (R2 n)))
         (Mux false (consbv (BV_full_adder_carry (R2 n) V2 false) nilbv)
            (consbv false nilbv)))) =
 BV_to_nat V2 * BV_to_nat (appbv (truncbv V1 n) (consbv false nilbv)).
intros.
simpl in |- *.
do 3 rewrite BV_to_nat_app2.
simpl in |- *.
elim mult_n_O.
elim mult_n_O.
elim plus_n_O.
elim plus_n_O.
rewrite (length_strip bool).
rewrite <- H.
clear H.
rewrite (length_app bool).
rewrite highs_is_strip.
rewrite (length_strip bool).
rewrite length_R1.
simpl in |- *.
replace (size - 1 + 1) with size.
rewrite minus_minus_lem2.
rewrite (strip_app bool).
rewrite BV_to_nat_app2.
rewrite (strip_strip bool).
rewrite (length_strip bool).
rewrite length_R1.
rewrite (length_strip bool).
rewrite BV_to_nat_app2.
rewrite (length_strip bool).
rewrite length_R1.
rewrite minus_minus_lem2.
replace (1 + (size - S n)) with (size - n).
rewrite minus_minus_lem2.
rewrite (minus_le_O (size - S n) (size - 1)).
rewrite (strip_O bool).
rewrite plus_assoc_reverse.
replace
 (power2 n * BV_to_nat (consbv (lowbit (R2 n)) nilbv) +
  power2 (S n) * BV_to_nat (highs (R2 n))) with (power2 n * BV_to_nat (R2 n)).
trivial with arith. symmetry  in |- *. apply BV_nat_lem1.
rewrite length_R2. exact size_not_O. exact H1. apply le_minus_minus; auto with arith.
exact H1. simpl in |- *. rewrite minus_Sn_m. auto with arith.
exact H0. exact H1. exact H1. rewrite length_R1. auto with arith. exact H1. 
rewrite length_R1. auto with arith. exact H1. exact H1. rewrite length_R1.
simpl in |- *. rewrite minus_Sn_m. simpl in |- *. auto with arith. exact H0. exact H1. 
exact H0. rewrite plus_comm. simpl in |- *. rewrite minus_Sn_m; auto with arith.
 exact H1. rewrite length_R1. auto with arith. exact H1. exact H1. 
rewrite (length_app bool). rewrite length_highs. rewrite length_R1.
simpl in |- *. rewrite plus_n_SO. replace (pred size) with (size - 1).
rewrite minus_Sn_m. simpl in |- *. elim minus_n_O. apply minus_le_lem2; auto with arith. auto with arith.
apply minus_n_SO. exact H1. apply (not_nil bool). rewrite length_R1; auto with arith.
Qed.

(****************************************************************)
(* Puis pour le cas ou R1[0]=true (tres tres long !!!!!)
*)

Lemma inv_ind_true :
 forall t n : nat,
 (n <= size ->
  BV_to_nat (appbv (stripbv (R1 n) (size - n)) (R2 n)) =
  BV_to_nat V2 * BV_to_nat (truncbv V1 n)) ->
 S n <= size ->
 n <= size ->
 BV_to_nat
   (appbv
      (stripbv
         (appbv (highs (R1 n))
            (Mux true (abit (BV_full_adder_sum (R2 n) V2 false) 0)
               (consbv (lowbit (R2 n)) nilbv))) (size - S n))
      (appbv (highs (Mux true (BV_full_adder_sum (R2 n) V2 false) (R2 n)))
         (Mux true (consbv (BV_full_adder_carry (R2 n) V2 false) nilbv)
            (consbv false nilbv)))) =
 BV_to_nat V2 * BV_to_nat (appbv (truncbv V1 n) (consbv true nilbv)).

intros. simpl in |- *. do 3 rewrite BV_to_nat_app2. simpl in |- *.
rewrite mult_plus_distr2.
rewrite
 (mult_plus_distr2 (BV_to_nat V2) (BV_to_nat (truncbv V1 n))
    (power2 (lengthbv (truncbv V1 n)) * 1)).
rewrite <- H. clear H. elim plus_n_O.
rewrite highs_is_strip. rewrite highs_is_strip.
rewrite (length_trunc bool). rewrite (length_strip bool).
 rewrite (length_app bool). rewrite (length_strip bool).
 rewrite (length_strip bool). rewrite length_abit.
 rewrite length_R1. rewrite (plus_comm (size - 1)).
 replace (1 + (size - 1)) with size.
rewrite minus_minus_lem2. rewrite length_BV_full_adder_sum.
rewrite length_R2. rewrite (strip_app bool).
 rewrite BV_to_nat_app2. rewrite (strip_strip bool).
 rewrite (length_strip bool). rewrite (length_strip bool).
 rewrite length_R1. rewrite BV_to_nat_app2.
simpl in |- *. rewrite minus_Sn_m.
 rewrite (minus_le_O (size - S n) (size - 1)).
simpl in |- *. rewrite minus_minus_lem2.
 rewrite (strip_O bool). rewrite (length_strip bool).
 rewrite length_R1. rewrite minus_minus_lem2.
replace (power2 n + power2 n) with (power2 (S n)).
replace (power2 n * 1) with (power2 n).
 rewrite <- (mult_assoc_reverse (power2 (S n))).
rewrite <- power2_plus. simpl in |- *. rewrite <- power2_eq2. rewrite <- power2_eq2.
replace (S (n + (size - 1))) with (n + size).
repeat rewrite plus_assoc_reverse.
replace
 (power2 n * BV_to_nat (abit (BV_full_adder_sum (R2 n) V2 false) 0) +
  (power2 (S n) * BV_to_nat (stripbv (BV_full_adder_sum (R2 n) V2 false) 1) +
   power2 (n + size) * bool_to_nat (BV_full_adder_carry (R2 n) V2 false)))
 with (power2 n * BV_to_nat (R2 n) + BV_to_nat V2 * power2 n).
trivial with arith. rewrite plus_assoc. rewrite <- highs_is_strip.
 unfold abit in |- *. unfold elemlist in |- *. rewrite (strip_O bool).
rewrite <- lowbit_is_trunc. rewrite BV_nat_lem1. rewrite power2_plus.
 rewrite (mult_assoc_reverse (power2 n)). rewrite <- mult_plus_distr2.
replace size with (lengthbv (BV_full_adder_sum (R2 n) V2 false)).
replace (bool_to_nat (BV_full_adder_carry (R2 n) V2 false)) with
 (BV_to_nat (consbv (BV_full_adder_carry (R2 n) V2 false) nilbv)).
rewrite <- BV_to_nat_app2.
replace
 (appbv (BV_full_adder_sum (R2 n) V2 false)
    (consbv (BV_full_adder_carry (R2 n) V2 false) nilbv)) with
 (BV_full_adder (R2 n) V2 false).
rewrite BV_full_adder_ok.
 rewrite mult_plus_distr2. rewrite mult_plus_distr2.
simpl in |- *. elim mult_n_O. elim plus_n_O. rewrite (mult_sym (BV_to_nat V2)).
 trivial with arith. unfold BV_full_adder in |- *. trivial with arith. 
simpl in |- *. elim plus_n_O. trivial with arith. rewrite length_BV_full_adder_sum; auto with arith.
rewrite length_R2; auto with arith. rewrite length_BV_full_adder_sum; auto with arith.
rewrite length_R2; auto with arith. rewrite length_R2; auto with arith. 
apply (not_nil bool); auto with arith. rewrite length_BV_full_adder_sum; auto with arith.
 rewrite length_R2; auto with arith. rewrite length_R2; auto with arith. 
replace (S (n + (size - 1))) with (S n + (size - 1)).
replace (S n + (size - 1)) with (n + S (size - 1)).
rewrite minus_Sn_m. simpl in |- *. elim minus_n_O. trivial with arith. 
auto with arith. rewrite plus_comm. simpl in |- *. rewrite plus_comm. trivial with arith.
simpl in |- *. trivial with arith. rewrite mult_sym. simpl in |- *. elim plus_n_O.
trivial with arith. auto with arith. exact H1. exact H1. rewrite length_R1; auto with arith.
 exact H1. apply le_minus_minus. auto with arith. exact H0. exact H1.
rewrite length_R1. auto with arith. exact H1. rewrite length_R1; auto with arith.
exact H1.
rewrite length_R2; auto with arith. exact H0. simpl in |- *. rewrite minus_Sn_m.
auto with arith. auto with arith. exact H1. rewrite length_BV_full_adder_sum; auto with arith.
unfold lt in |- *. rewrite length_R2. auto with arith. exact H1. transitivity size; auto with arith. 
rewrite length_BV_full_adder_sum; auto with arith. rewrite length_R2; auto with arith.
 rewrite length_R2; auto with arith. rewrite length_R1; auto with arith. 
rewrite (length_app bool). rewrite (length_strip bool).
rewrite length_R1; auto with arith. rewrite length_abit. rewrite plus_comm.
simpl in |- *. rewrite minus_Sn_m. simpl in |- *. elim minus_n_O. apply minus_le_lem2. auto with arith.
rewrite length_BV_full_adder_sum; auto with arith. rewrite length_R2; auto with arith.
 rewrite length_R2; auto with arith. rewrite length_R1; auto with arith. 
replace (length V1) with (lengthbv V1); auto with arith.
rewrite length_V1_size. exact H1. exact H1. 

Qed.

(****************************************************************)
(* Finalement on prouve le cas general de l'invariant:
*)

Lemma Invariant :
 forall t : nat,
 t <= size ->
 BV_to_nat (appbv (stripbv (R1 t) (size - t)) (R2 t)) =
 BV_to_nat V2 * BV_to_nat (truncbv V1 t).

simple induction t. intros. elim minus_n_O. apply Invariant_t_O.
intros. rewrite <- (app_trunc_elemlist bool).
replace (elemlist bool V1 n) with (abit V1 n).
rewrite <- (R1_lem3 n). rewrite R1_eq2. rewrite R2_eq2.
rewrite <- lowbit_is_abit. case (lowbit (R1 n)).
replace (consbv (lowbit (BV_full_adder_sum (R2 n) V2 false)) nilbv) with
 (abit (BV_full_adder_sum (R2 n) V2 false) 0).
apply inv_ind_true. auto with arith.
intros. apply H. exact H1. exact H0.
apply le_Sn_le; exact H0. unfold abit in |- *. rewrite lowbit_is_trunc.
unfold elemlist in |- *. rewrite (strip_O bool). trivial with arith.
apply (not_nil bool). rewrite length_BV_full_adder_sum. rewrite length_R2.
exact size_not_O. apply le_Sn_le; exact H0.
rewrite length_R2. rewrite length_V2_size. trivial with arith.
apply le_Sn_le; exact H0.
replace (consbv (lowbit (BV_full_adder_sum (R2 n) V2 false)) nilbv) with
 (abit (BV_full_adder_sum (R2 n) V2 false) 0).
apply inv_ind_false. trivial with arith.
exact H. exact H0. apply le_Sn_le; exact H0. rewrite lowbit_is_trunc.
unfold abit in |- *. unfold elemlist in |- *. rewrite (strip_O bool). trivial with arith.
apply (not_nil bool).
rewrite length_BV_full_adder_sum. rewrite length_R2; auto with arith.
transitivity size.
rewrite length_R2; trivial with arith. apply le_Sn_le; exact H0. auto with arith.
apply (not_nil bool). rewrite length_R1; auto with arith. auto with arith. auto with arith.
replace (length V1) with (lengthbv V1). rewrite length_V1_size. exact H0.
auto with arith.

Qed.

(****************************************************************)
(* Et le theoreme final qui est une specialisation de l'invariant
   avec t=size *)

Theorem Correct :
 BV_to_nat (appbv (R1 size) (R2 size)) = BV_to_nat V2 * BV_to_nat V1.

intros. rewrite <- (strip_O bool (R1 size)).
replace (BV_to_nat V1) with (BV_to_nat (truncbv V1 size)).
rewrite (minus_n_n size). apply Invariant. auto with arith.
rewrite <- length_V1_size. rewrite (trunc_all bool). trivial with arith.
Qed.