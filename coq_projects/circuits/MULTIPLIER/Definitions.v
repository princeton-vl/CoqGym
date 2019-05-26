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
(* file: Definitions.v                                          *)
(* contents: PROOF OF A SEQUENTIAL MULTIPLIER. Definitions of   *)
(* auxilliary functions, axioms and the register-functions.     *)
(****************************************************************)

(****************************************************************)
(* Definitions des operateurs utilises (lowbit et highs)
   des registres (R1 et R2)
   et des lemmes sur les longueurs des registres
*)

Require Export BV.
Require Export Adder.
Require Import Gt.

Definition Mux := If BV.
Hint Unfold Mux.


Definition lowbit (l : list bool) :=
  match l with
  | nil => false
  | b :: _ => b
  end.

Definition highs (l : list bool) :=
  match l with
  | nil => nil (A:=bool)
  | _ :: v => v
  end.

Lemma lowbit_is_trunc :
 forall v : BV, v <> nilbv -> consbv (lowbit v) nilbv = truncbv v 1.
simple induction v. intro. absurd (nil <> nilbv); unfold not in |- *; auto with arith.
intros. simpl in |- *. rewrite (trunc_O bool). trivial with arith.
Qed.

Lemma lowbit_is_abit :
 forall v : BV, v <> nilbv -> consbv (lowbit v) nilbv = abit v 0.
intros. unfold abit in |- *. unfold elemlist in |- *. rewrite strip_O.
apply lowbit_is_trunc. exact H.
Qed.

Lemma highs_is_strip : forall v : BV, highs v = stripbv v 1.
simple induction v. simpl in |- *. auto with arith.
intros. simpl in |- *. rewrite (strip_cons_S bool). rewrite strip_O. trivial with arith.
Qed.

Lemma app_lowbit_highs :
 forall v : BV, v <> nilbv -> appbv (consbv (lowbit v) nilbv) (highs v) = v.
intros. rewrite lowbit_is_trunc. rewrite highs_is_strip.
rewrite (app_trunc_strip bool). trivial with arith. exact H.
Qed.

Lemma length_highs :
 forall v : BV, v <> nilbv -> lengthbv (highs v) = pred (lengthbv v).
intros. rewrite highs_is_strip.
rewrite (length_strip bool). apply minus_n_SO.
apply (v_not_nil_length bool). exact H.
Qed.

Lemma length_abit :
 forall (v : BV) (i : nat), i < lengthbv v -> lengthbv (abit v i) = 1.
unfold abit in |- *. exact (length_elemlist bool).
Qed.
(****************************************************************)
(* Defintitions des variables et leurs contraintes *)

Parameter size : nat. (* La taille des mots *)
Parameter V1 : BV. (* Les deux entrees *)
Parameter V2 : BV.

Axiom size_not_O : size <> 0. Hint Resolve size_not_O.
Axiom length_V1_size : lengthbv V1 = size. Hint Resolve length_V1_size.
Axiom length_V2_size : lengthbv V2 = size. Hint Resolve length_V2_size.

Lemma le_SO_size : 1 <= size.
       generalize size_not_O. elim size. intro. absurd (0 <> 0); unfold not in |- *; auto with arith.
       intros. apply le_n_S. auto with arith. Qed. Hint Resolve le_SO_size.

Lemma length_V1 : lengthbv V1 <> 0.
	rewrite length_V1_size. auto with arith. Qed. Hint Resolve length_V1.
Lemma length_V2 : lengthbv V2 <> 0.
	rewrite length_V2_size. auto with arith. Qed. Hint Resolve length_V2.
Lemma length_V2_V1 : lengthbv V2 = lengthbv V1.
	transitivity size; auto with arith. Qed.
Lemma V1_not_nil : V1 <> nilbv.
	apply (not_nil bool). auto with arith. Qed. Hint Resolve V1_not_nil.
Lemma V2_not_nil : V2 <> nilbv.
	apply (not_nil bool). auto with arith. Qed. Hint Resolve V2_not_nil.
Lemma le_SO_length_V1 : 1 <= lengthbv V1.
	apply (le_SO_length_v bool). auto with arith. Qed. Hint Resolve le_SO_length_V1.

(****************************************************************)
(* Les registres: *)

Fixpoint R1 (st : nat) : BV :=
  match st return BV with
  | O => V1
  | S t =>
      appbv (highs (R1 t))
        (Mux (lowbit (R1 t))
           (consbv (lowbit (BV_full_adder_sum (R2 t) V2 false)) nilbv)
           (consbv (lowbit (R2 t)) nilbv))
  end
 
 with R2 (st : nat) : BV :=
  match st return BV with
  | O => BV_null size
  | S t =>
      appbv
        (highs
           (Mux (lowbit (R1 t)) (BV_full_adder_sum (R2 t) V2 false) (R2 t)))
        (Mux (lowbit (R1 t))
           (consbv (BV_full_adder_carry (R2 t) V2 false) nilbv)
           (consbv false nilbv))
  end.


Lemma R1_eq1 : R1 0 = V1. auto with arith. Qed.
Lemma R1_eq2 :
 forall t : nat,
 R1 (S t) =
 appbv (highs (R1 t))
   (Mux (lowbit (R1 t))
      (consbv (lowbit (BV_full_adder_sum (R2 t) V2 false)) nilbv)
      (consbv (lowbit (R2 t)) nilbv)).
auto with arith. Qed.

Lemma R2_eq1 : R2 0 = BV_null size. auto with arith. Qed.
Lemma R2_eq2 :
 forall t : nat,
 R2 (S t) =
 appbv
   (highs (Mux (lowbit (R1 t)) (BV_full_adder_sum (R2 t) V2 false) (R2 t)))
   (Mux (lowbit (R1 t)) (consbv (BV_full_adder_carry (R2 t) V2 false) nilbv)
      (consbv false nilbv)).
auto with arith. Qed.

(****************************************************************)
Lemma length_R1 : forall t : nat, t <= size -> lengthbv (R1 t) = size.
simple induction t. auto with arith.
intros. rewrite R1_eq2. rewrite (length_app bool).
unfold Mux in |- *. rewrite (F_If BV nat _ _ _ (@length bool)). simpl in |- *. rewrite If_eq.
rewrite highs_is_strip. rewrite (length_strip bool). unfold lengthbv in H.
rewrite H. symmetry  in |- *. rewrite plus_comm. apply le_plus_minus. auto with arith.
apply le_Sn_le; auto with arith.
unfold lengthbv in H. rewrite H. auto with arith.
apply le_Sn_le. exact H0.
Qed. Hint Resolve length_R1.

Lemma length_R2 : forall t : nat, t <= size -> lengthbv (R2 t) = size.
simple induction t. simpl in |- *.
unfold lengthbv, BV_null in |- *. rewrite (length_list_const bool). trivial with arith.
unfold lengthbv in |- *. intros. rewrite R2_eq2.
rewrite (length_app bool). unfold Mux, consbv. 
rewrite (F_If BV BV _ _ _ highs). 
rewrite (F_If BV nat _ _ _ (@length bool)).
rewrite highs_is_strip. rewrite (length_strip bool).
rewrite length_BV_full_adder_sum. unfold lengthbv in |- *.
rewrite H. rewrite highs_is_strip. rewrite (length_strip bool).
rewrite H. rewrite If_eq. rewrite (F_If BV nat _ _ _ (@length bool)). simpl in |- *.
rewrite If_eq. symmetry  in |- *. rewrite plus_comm. apply le_plus_minus. auto with arith.
auto with arith. rewrite H. auto with arith.
apply le_Sn_le; exact H0. apply le_Sn_le; exact H0.
unfold lengthbv in |- *. rewrite H. auto with arith. apply le_Sn_le; exact H0.
rewrite length_BV_full_adder_sum.
unfold lengthbv in |- *. rewrite H. auto with arith. apply le_Sn_le; exact H0.
unfold lengthbv in |- *. rewrite H. auto with arith. apply le_Sn_le; exact H0.
Qed. Hint Resolve length_R2.

Lemma R1_never_nil : forall t : nat, t <= size -> R1 t <> nilbv.
intros. apply (not_nil bool). rewrite length_R1. auto with arith. exact H.
Qed.

