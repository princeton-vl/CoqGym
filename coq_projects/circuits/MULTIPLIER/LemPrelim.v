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
(* file: LemPrelim.v                                            *)
(* contents: VERIFICATION OF A SEQUENTIAL MULTIPLIER. Proofs of *)
(* some preliminary lemmas.                                     *)
(****************************************************************)

(* Des lemmes preliminaires *)

Require Export Definitions.

Lemma R1_lem :
 forall t : nat, (* R1(t)[0:n-1-t]=B[t:n-1] *)
 t <= size -> truncbv (R1 t) (size - t) = stripbv V1 t.
simple induction t. elim minus_n_O. rewrite <- (length_R1 0).
intro. rewrite (trunc_all bool). rewrite (strip_O bool). auto with arith.
auto with arith. intros. rewrite R1_eq2. rewrite highs_is_strip.
rewrite (trunc_app bool). rewrite (trunc_strip bool).
rewrite (length_strip bool). rewrite length_R1.
replace (size - S n - (size - 1)) with 0.
rewrite (trunc_O bool).
replace (1 + (size - S n)) with (size - n).
rewrite (app_v_nil bool). unfold truncbv in H.
rewrite H. rewrite (strip_strip bool). rewrite plus_comm. simpl in |- *. auto with arith.
apply le_Sn_le; exact H0.
simpl in |- *. rewrite minus_Sn_m. simpl in |- *. trivial with arith.
exact H0.
symmetry  in |- *. apply minus_le_O. apply le_minus_minus. auto with arith.
apply le_Sn_le; exact H0.
rewrite length_R1. apply le_SO_size. apply le_Sn_le; exact H0.
Qed.

(*
Lemma R1_lem2 : (t,i:nat) (* R1(t)[i]=B[t+i] *)
	(le t size) -> (lt i size)  ->
	(abit (R1 t) i) = (abit v1 (plus t i)).
*)


Lemma R1_lem3 :
 forall t : nat, (* R1(t)[0]=B[t] *)
 t < size -> abit (R1 t) 0 = abit V1 t.
intros. unfold abit in |- *. unfold elemlist in |- *.
apply (trunc_plus_petit bool) with (size - t).
unfold lt in H. inversion H. rewrite <- minus_Sn_m. auto with arith. auto with arith.
rewrite <- minus_Sn_m. auto with arith. apply le_Sn_le; auto with arith.
rewrite (strip_O bool). apply R1_lem. apply lt_le_weak. exact H.
Qed.

(****************************************************************)

Lemma lem_le_minus_v1_Sn :
 forall n : nat,
 S n <= size ->
 n <= size ->
 size - S n <= lengthbv (appbv (highs (R1 n)) (consbv (lowbit (R2 n)) nilbv)).

intros. rewrite (length_app bool).
rewrite highs_is_strip. rewrite (length_strip bool). rewrite length_R1.
simpl in |- *. rewrite plus_comm. rewrite <- le_plus_minus. apply minus_le_lem2.
exact le_SO_size. exact H0. rewrite length_R1. exact le_SO_size. exact H0.
Qed.

Lemma BV_to_nat_lem0 :
 forall v : BV,
 lengthbv v <> 0 ->
 BV_to_nat v =
 BV_to_nat (consbv (lowbit v) nilbv) + power2 1 * BV_to_nat (highs v).

intros. rewrite lowbit_is_trunc. rewrite highs_is_strip.
replace (power2 1) with (power2 (length (trunc bool v 1))).
rewrite <- BV_to_nat_app2. rewrite (app_trunc_strip bool). trivial with arith.
rewrite (length_trunc bool). trivial with arith.
apply (le_SO_length_v bool). exact H. apply (not_nil bool). exact H.
Qed.

Lemma BV_nat_lem1 :
 forall (v : BV) (n : nat),
 lengthbv v <> 0 ->
 power2 n * BV_to_nat (consbv (lowbit v) nilbv) +
 power2 (S n) * BV_to_nat (highs v) = power2 n * BV_to_nat v.

intros. rewrite power2_eq2. rewrite mult_plus_distr_r.
replace (BV_to_nat v) with
 (BV_to_nat (appbv (consbv (lowbit v) nilbv) (highs v))).
rewrite BV_to_nat_app2.
rewrite
 (mult_sym (power2 n)
    (BV_to_nat (consbv (lowbit v) nilbv) +
     power2 (lengthbv (consbv (lowbit v) nilbv)) * BV_to_nat (highs v)))
 .
rewrite mult_plus_distr_r.
simpl in |- *. elim plus_n_O. elim plus_n_O. rewrite mult_plus_distr_r.
rewrite (mult_sym (power2 n)). rewrite (mult_sym (power2 n)). trivial with arith.
rewrite app_lowbit_highs. trivial with arith.
apply (not_nil bool). exact H.
Qed.
