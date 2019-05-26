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
   dec.
   Some utilities for proving decidability of predicates.

   @author Olga Caprotti and Martijn Oostdijk
   @version $Revision$
*)

Require Import Arith.
Require Import ZArith.
Require Import EqNat.

(** Checks that all nats before n are P *)

Fixpoint allbefore (P : nat -> Prop) (n : nat) {struct n} : Prop :=
  match n with
  | O => True
  | S x => allbefore P x /\ P x
  end.

(** Checks that some nat before n is P *)

Fixpoint exbefore (P : nat -> Prop) (n : nat) {struct n} : Prop :=
  match n with
  | O => False
  | S x => exbefore P x \/ P x
  end.

Theorem allbefore_ok :
 forall (P : nat -> Prop) (n : nat),
 (forall q : nat, q < n -> P q) <-> allbefore P n.
Proof.
   intro.
   simple induction n.
   simpl in |- *.
   split.
   tauto.
   intros.
   elim (lt_n_O q).
   assumption.
   simpl in |- *.
   intros m IHm.
   elim IHm.
   intros.
   split.
   intros.
   split.
   apply H.
   intros.
   apply (H1 q).
   unfold lt in |- *.
   unfold lt in H2.
   apply le_S.
   assumption.
   apply (H1 m).
   unfold lt in |- *.
   apply le_n.
   intro.
   elim H1.
   intro.
   intro.
   intros.
   elim (le_lt_or_eq q m).
   intros.
   apply H0.
   assumption.
   assumption.
   intros.
   rewrite H5.
   assumption.
   unfold lt in H4.
   apply (le_S_n q m).
   assumption.
Qed.

Theorem exbefore_ok :
 forall (P : nat -> Prop) (n : nat),
 (exists q : nat, q < n /\ P q) <-> exbefore P n.
Proof.
   intro P.
   simple induction n.
   simpl in |- *.
   split.
   intros.
   elim H.
   intros.
   elim H0.
   intros.
   elim (lt_n_O x).
   assumption.
   intros.
   elim H.
   intros m IHm.
   simpl in |- *.
   elim IHm.
   intros.
   split.
   intro.
   elim H1.
   intro.
   intros.
   elim H2.
   intros.
   elim (le_lt_or_eq x m).
   intros.
   left.
   apply H.
   split with x.
   split.
   assumption.
   assumption.
   intros.
   right.
   rewrite H5 in H4.
   assumption.
   apply (le_S_n x m).
   assumption.
   intros.
   elim H1.
   intros.
   case H0.
   assumption.
   intros.
   split with x.
   elim H3.
   intros.
   split.
   unfold lt in |- *.
   unfold lt in H4.
   apply le_S.
   assumption.
   assumption.
   intros.
   split with m.
   split.
   unfold lt in |- *.
   apply le_n.
   assumption.
Qed.


(** some decidable relations on nat *)

Lemma eqdec : forall n m : nat, n = m \/ n <> m.
Proof.
   simple induction n.
   intro.
   case m.
   left.
   reflexivity.
   right.
   discriminate.
   intros.
   case m.
   right.
   discriminate.
   intro m0.
   elim (H m0).
   left.
   rewrite H0.
   reflexivity.
   right.
   intro.
   apply H0.
   inversion H1.
   reflexivity.
Qed.

Lemma ledec : forall n m : nat, n <= m \/ ~ n <= m.
Proof.
   intros. elim (le_or_lt n m).
   left. assumption.
   right. apply lt_not_le. assumption.
Qed.

Lemma ltdec : forall n m : nat, n < m \/ ~ n < m.
Proof.
   unfold lt in |- *. intros. apply ledec.
Qed.

Lemma gedec : forall n m : nat, n >= m \/ ~ n >= m.
Proof.
   unfold ge in |- *. intros. apply ledec.
Qed.

Lemma gtdec : forall n m : nat, n > m \/ ~ n > m.
Proof.
   unfold gt in |- *. intros. apply ltdec.
Qed.

(** relations on Z *)

Lemma zeqdec : forall x y : Z, x = y \/ x <> y.
Proof.
   intros. elim (dec_eq x y). left. assumption. right. assumption.
Qed.

(** the connectives preserve decidability *)

Lemma notdec : forall P : Prop, P \/ ~ P -> ~ P \/ ~ ~ P.
Proof.
   intros. elim H.
   right. intro.  apply H1. assumption.
   left. assumption.
Qed.

Lemma anddec :
 forall P Q : Prop, P \/ ~ P -> Q \/ ~ Q -> P /\ Q \/ ~ (P /\ Q).
Proof.
   intros. elim H. elim H0.
   left. split. assumption. assumption.
   right. intro. apply H1. elim H3. intros. assumption.
   right. intro. apply H1. elim H2. intros. assumption.
Qed.

Lemma ordec :
 forall P Q : Prop, P \/ ~ P -> Q \/ ~ Q -> (P \/ Q) \/ ~ (P \/ Q).
Proof.
   intros. elim H.
   left. left. assumption.
   elim H0.
   left. right. assumption.
   right. intro. elim H3. assumption. assumption.
Qed.

Lemma impdec :
 forall P Q : Prop, P \/ ~ P -> Q \/ ~ Q -> (P -> Q) \/ ~ (P -> Q).
Proof.
   intros. elim H.
   elim H0.
   left. intros. assumption.
   right. intro. apply H1. apply H3. assumption.
   left. intros. elim H1. assumption.
Qed.

Lemma iffdec :
 forall P Q : Prop, P \/ ~ P -> Q \/ ~ Q -> (P <-> Q) \/ ~ (P <-> Q).
Proof.
   unfold iff in |- *. intros.
   apply anddec.
   apply impdec. assumption. assumption.
   apply impdec. assumption. assumption.
Qed.

(** bounded quantifiers preserve decidability *)

Theorem alldec :
 forall (P : nat -> Prop) (N : nat),
 (forall n : nat, P n \/ ~ P n) ->
 (forall x : nat, x < N -> P x) \/ ~ (forall x : nat, x < N -> P x).
Proof.
   intro P. simple induction N.
   left. intros. elim (lt_n_O x). assumption.
   intros M IH decP.
   elim IH. elim (decP M).
   left. intros. unfold lt in H1. elim (le_lt_or_eq x M). intros.
   apply H0. assumption.
   intros. rewrite H2. assumption.
   apply le_S_n. assumption.
   right. intro. apply H. apply H1. apply lt_n_Sn.
   right. intro. apply H. intros. apply H0. apply lt_S. assumption.
   assumption.
Qed.

Theorem exdec :
 forall (P : nat -> Prop) (N : nat),
 (forall n : nat, P n \/ ~ P n) ->
 (exists x : nat, x < N /\ P x) \/ ~ (exists x : nat, x < N /\ P x).
Proof.
   intro P. simple induction N.
   intro decP.
   right. intro. elim H. intros. elim H0. intros. elim (lt_n_O x). assumption.
   intros M IH decP.
   elim IH. left.
   elim H. intros. split with x. elim H0. intros.
   split.
   apply lt_S. assumption.
   assumption.
   intros.
   elim (decP M).
   left. split with M. split. apply lt_n_Sn.
   assumption.
   right. intro.
   elim H1. intros. elim H2. intros.
   unfold lt in H3. elim (le_lt_or_eq x M).
   intro. apply H. split with x. split. assumption.
   assumption.
   intro. apply H0. rewrite <- H5. assumption.
   apply le_S_n. assumption.
   assumption.
Qed.

(** De Morgan's law holds for decidable P if the quantifiers are bounded *)

Theorem decDeMorgan :
 forall (N : nat) (P : nat -> Prop),
 (forall n : nat, P n \/ ~ P n) ->
 ((exists x : nat, x < N /\ P x) <-> ~ (forall x : nat, x < N -> ~ P x)).
Proof.
   split.
   intro.
   elim H0.
   intros.
   intro.
   elim H1.
   intros.
   apply (H2 x H3 H4).
   elim N. intros. elim H0. intros. elim (lt_n_O x). assumption.
   intros M IH. intros.
   elim (H M).
   intros.
   split with M.
   split.
   apply lt_n_Sn.
   assumption.
   intros.
   cut (~ (forall x : nat, x < M -> ~ P x)).
   intros.
   elim IH.
   intros.
   split with x.
   elim H3.
   intros.
   split.
   apply lt_S.
   assumption.
   assumption.
   assumption.
   intro.
   apply H0.
   intros.
   elim (le_lt_or_eq x M).
   intros.
   apply H2.
   assumption.
   intros.
   rewrite H4.
   assumption.
   unfold lt in H3.
   apply le_S_n.
   assumption.
Qed.


(** Some nice boolean stuff... *)

Definition istrue (b : bool) := if b then True else False.

Lemma beq_nat_ok : forall n m : nat, n = m <-> istrue (beq_nat n m).
Proof.
   simple induction n.
   intro m. case m. simpl in |- *. tauto. simpl in |- *. split. discriminate. tauto.
   intros.
   case m. simpl in |- *. split. discriminate. tauto.
   intros. elim (H n1).
   split.
   intros. simpl in |- *. apply H0. injection H2. tauto.
   simpl in |- *. intros. rewrite (H1 H2). reflexivity.
Qed.

Lemma beq_nat_eq : forall n m : nat, n = m <-> beq_nat n m = true.
Proof.
   simple induction n.
   intro. case m.
   simpl in |- *. split. reflexivity. reflexivity.
   simpl in |- *. split. intro. discriminate. intro. discriminate.
   intros n1 IH. intro m. case m.
   simpl in |- *. split. intro. discriminate. intro. discriminate.
   intro m1. intros. simpl in |- *.
   elim (IH m1). split.
   intro. injection H1. assumption.
   intros. rewrite H0. reflexivity. assumption.
Qed.

Lemma beq_nat_neq : forall n m : nat, n <> m <-> beq_nat n m = false.
Proof.
   simple induction n.
   intro. case m. simpl in |- *. split.
   intro. elim H. reflexivity. intro. discriminate.
   intro m1. simpl in |- *. split. reflexivity. intro. discriminate.
   intros n1 IH. intro m. case m.
   simpl in |- *. split. reflexivity. intro. discriminate.
   intro m1. simpl in |- *.
   elim (IH m1). split.
   intro. apply H. intro. elim H1. rewrite H2. reflexivity.
   intro. intro. elim H0. assumption. injection H2. intro. assumption.
Qed.

Lemma zeq_bool_eq : forall x y : Z, x = y <-> Zeq_bool x y = true.
Proof.
   intros. elim (Zcompare_Eq_iff_eq x y). intros. unfold Zeq_bool in |- *. split.

   (* -> *)
   intro. rewrite H0.
   reflexivity. assumption.

   (* <- *)
   intro. apply H. generalize H1.
   elim (x ?= y)%Z.
   intro. reflexivity.
   intro. discriminate H2.
   intro. discriminate H2.
Qed.

Lemma zeq_bool_neq : forall x y : Z, x <> y <-> Zeq_bool x y = false.
Proof.
   intros. elim (Zcompare_Eq_iff_eq x y). intros. unfold Zeq_bool in |- *. split.

   (* -> *)
   generalize H0. generalize H. elim (x ?= y)%Z.
   intros. elim H3. apply H1. reflexivity.
   intros. reflexivity.
   intros. reflexivity.

   (* <- *)
   intros. generalize H1. generalize H0. elim (x ?= y)%Z.
   intros. discriminate H3.
   intros. intro. cut (Datatypes.Lt = Datatypes.Eq). discriminate.
   apply H2. assumption.
   intros. intro. cut (Datatypes.Gt = Datatypes.Eq). discriminate.
   apply H2. assumption.
Qed.
