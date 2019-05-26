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


(**
   prime.
   The primality predicate.
 
   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import ZArith.
Require Import Wf_nat.

Require Import lemmas.
Require Import natZ.
Require Import dec.
Require Import divides.
Require Import modulo.
Require Import list.


(** * Primality on nat *)

Definition Prime (n : nat) : Prop :=
  n > 1 /\ (forall q : nat, Divides q n -> q = 1 \/ q = n).

(** Prime with bounded all quantifier. *)

Definition bPrime (n : nat) :=
  n > 1 /\ (forall q : nat, q < S n -> Divides q n -> q = 1 \/ q = n).

Lemma primebprime : forall n : nat, Prime n <-> bPrime n.
Proof.
   unfold Prime, bPrime in |- *.
   split.
   intro. elim H.
   split.
   assumption.
   intros.
   apply H1.
   assumption.
   intro. elim H.
   split.
   assumption.
   intros.
   apply H1.
   unfold lt in |- *.
   apply le_n_S.
   apply div_le.
   apply lt_trans with 1. apply lt_O_Sn. assumption.
   assumption.
   assumption.
Qed.

(** Prime is decidable. *)

Lemma bprimedec : forall n : nat, bPrime n \/ ~ bPrime n.
Proof.
   unfold bPrime in |- *. intros.
   apply anddec.
   apply gtdec.
   apply (alldec (fun q : nat => Divides q n -> q = 1 \/ q = n) (S n)).
   intros.
   apply impdec.
   apply divdec.
   apply ordec.
   apply eqdec.
   apply eqdec.
Qed.

Lemma primedec : forall n : nat, Prime n \/ ~ Prime n.
Proof.
   intro. elim (primebprime n).
   intros. elim (bprimedec n).
   left. apply (H0 H1).
   right. intro. apply H1. apply (H H2).
Qed.

(** Non-primes n>1 have non-trivial divisors. *)

Lemma nonprime_witness :
 forall n : nat,
 n > 1 -> ~ Prime n -> exists d : nat, 1 < d /\ d < n /\ Divides d n.
Proof.
   intro n. case n.
   intro. elim (lt_n_O 1). assumption.
   intro n1. case n1. intro. elim (lt_irrefl 1). assumption.
   intro n2. intros.
   elim
    (decDeMorgan (S (S n2)) (fun d : nat => 1 < d /\ Divides d (S (S n2)))).
   intros. elim H2. intros.
   split with x.
   elim H3. intros.
   elim H5. intros.
   split.
   assumption.
   split.
   assumption.
   assumption.
   intro. apply H0. unfold Prime in |- *. split. assumption.
   intro q. case q.
   intro. unfold Divides in H4. elim H4. simpl in |- *. intros. discriminate H5.
   intro q1. case q1. left. reflexivity.
   intro q2. intros. right.
   elim (le_lt_or_eq (S (S q2)) (S (S n2))).
   intros. elim (H3 (S (S q2))). assumption.
   split. apply lt_n_S. apply lt_O_Sn. assumption.
   intros. assumption.
   apply div_le1. assumption.
   intros. apply anddec. apply ltdec. apply divdec.
Qed.

Lemma nonprime_sqrwitness :
 forall n : nat,
 n > 1 -> ~ Prime n -> exists d : nat, 1 < d /\ d * d <= n /\ Divides d n.
Proof.
   intros. elim (nonprime_witness n).
   intro d. intros.
   elim (sqrdivbound n d). intro d'. intros.
   elim H2. intros.
   elim H4. intros.
   elim H6.
   intro. split with d'.
   split. rewrite H7. elim H1. tauto.
   split. assumption.
   rewrite H7. elim H1. tauto.
   intro. split with d'. split. apply (lt_n_nm_m_gt_1 d d').
   rewrite H7. elim H1. tauto.
   split. assumption.
   assumption.
   elim H1. tauto.
   assumption.
   assumption.
Qed.

(** Non-primes n>1 have prime-divisors. *)

Theorem nonprime_primewitness :
 forall n : nat,
 n > 1 ->
 ~ Prime n -> exists d : nat, 1 < d /\ d * d <= n /\ Divides d n /\ Prime d.
Proof.
   intro. apply (lt_wf_ind n).
   intros N IH. intros.
   elim (nonprime_sqrwitness N). intro x. intros.
   elim H1. intros.
   elim H3. intros.
   elim (primedec x).
   intros.
   split with x.
   split. assumption.
   split. assumption.
   split. assumption.
   assumption.
   intros. elim (IH x). intros.
   elim H7. intros.
   elim H9. intros.
   elim H11.
   intros.
   split with x0.
   split. assumption.
   split. apply le_trans with (x * x).
   apply le_trans with x. assumption. apply le_n_nn. assumption.
   split. apply div_trans with x. assumption. assumption.
   assumption.
   unfold lt in |- *. apply le_trans with (x * x).
   change (x < x * x) in |- *. apply sqr_ascend. assumption.
   assumption. assumption. assumption. assumption. assumption.
Qed.

(** Prime(n) if all prime divisors > sqrt(n). *)

Theorem primepropdiv :
 forall n : nat,
 n > 1 -> (forall q : nat, Prime q -> Divides q n -> q * q > n) -> Prime n.
Proof.
   intros. elim (primedec n).
   intro. assumption.
   intros. elim (nonprime_primewitness n).
   intros.
   elim H2. intros.
   elim H4. intros.
   elim H6. intros.
   elim (le_not_lt (x * x) n).
   assumption.
   unfold gt in H0. apply H0. assumption. assumption.
   assumption.
   assumption.
Qed.

Lemma primediv1p : forall p n : nat, Prime p -> Divides n p -> n = 1 \/ n = p.
Proof.
   intros.
   unfold Prime in H. elim H. intros.
   apply (H2 n). assumption.
Qed.

(** Two is a prime. *)

Lemma prime2 : Prime 2.
Proof.
   apply primepropdiv.
   auto.
   intro q. case q.
   intros. elim H. intro.
   elim (lt_n_O 1). assumption.
   intro q1. case q1.
   intros. elim H. intro.
   elim (lt_irrefl 1). assumption.
   intro q2. case q2.
   simpl in |- *. intros. auto.
   intro q3. simpl in |- *. intros.
   repeat apply gt_n_S. apply gt_Sn_O.
Qed.

(** * Primality on Z *)

(** ZPrime, just like Prime but uses only Z. *)

Definition ZPrime (n : Z) : Prop :=
  (n > 1)%Z /\ (forall q : Z, (q >= 0)%Z -> ZDivides q n -> q = 1%Z \/ q = n).

Lemma primezprime : forall n : nat, Prime n -> ZPrime (Z_of_nat n).
Proof.
   unfold Prime, ZPrime in |- *. intros.
   elim H. intros. split.
   change (Z_of_nat n > Z_of_nat 1)%Z in |- *.
   apply Znat.inj_gt. assumption.
   intros. elim (H1 (Zabs_nat q)).
   left. rewrite <- (inj_abs_pos q). rewrite H4.
   simpl in |- *. reflexivity. assumption.
   right. rewrite <- (inj_abs_pos q). rewrite H4.
   reflexivity. assumption.
   rewrite <- (abs_inj n).
   apply zdivdiv. assumption.
Qed.

Lemma zprimeprime : forall n : Z, ZPrime n -> Prime (Zabs_nat n).
Proof.
   unfold ZPrime, Prime in |- *. intros.
   elim H. intros. split.
   change (Zabs_nat n > Zabs_nat 1) in |- *.
   apply gtzgt.
   apply Zle_trans with 1%Z.
   unfold Zle in |- *. simpl in |- *. discriminate.
   apply Zlt_le_weak. apply Zgt_lt. assumption.
   unfold Zle in |- *. simpl in |- *. discriminate.
   assumption.
   intros. elim (H1 (Z_of_nat q)).
   left. rewrite <- (abs_inj q). rewrite H3.
   simpl in |- *. reflexivity.
   right. rewrite <- (abs_inj q). rewrite H3.
   reflexivity. apply nat_ge_0.
   apply divzdiv. rewrite abs_inj. assumption.
Qed.

Lemma zprime2 : ZPrime 2.
Proof.
   change (ZPrime (Z_of_nat 2)) in |- *.
   apply primezprime.
   exact prime2.
Qed.

Lemma zprime2a : ZPrime 2.
Proof.
   exact zprime2.
Qed.

(** All numbers in natlist are prime. *)

Definition allPrime : natlist -> Prop := alllist nat Prime.

Definition allZPrime : Zlist -> Prop := alllist Z ZPrime.

Lemma allzprimeallpos : forall l : Zlist, allZPrime l -> allPos l.
Proof.
   unfold allZPrime, allPos in |- *.
   simple induction l.
   simpl in |- *. intro. assumption.
   simpl in |- *. intros h t IH H.
   elim H. intros. elim H0. intros.
   split. apply Zle_ge. apply Zle_trans with 1%Z.
   unfold Zle in |- *. simpl in |- *. discriminate.
   apply Zlt_le_weak. apply Zgt_lt. assumption.
   apply IH. assumption.
Qed.

Lemma allprimeallzprime :
 forall l : natlist, allPrime l -> allZPrime (map _ _ Z_of_nat l).
Proof.
   unfold allPrime, allZPrime in |- *.
   simple induction l.
   simpl in |- *. intro. assumption.
   simpl in |- *. intros h t IH H. elim H. intros. split.
   apply primezprime. assumption.
   apply IH. assumption.
Qed.

Lemma allzprimeallprime :
 forall l : Zlist, allZPrime l -> allPrime (map _ _ Zabs_nat l).
Proof.
   unfold allPrime, allZPrime in |- *.
   simple induction l.
   simpl in |- *. intro. assumption.
   simpl in |- *. intros h t IH H. elim H. intros. split.
   apply zprimeprime. assumption.
   apply IH. assumption.
Qed.
