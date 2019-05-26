(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** MM reduces to FRACTRAN *)

Require Import List Arith Omega.

Require Import ILL.Definitions.

Require Import pos vec.
Require Import sss subcode mm_defs.
Require Import fractran_defs prime_seq mm_fractran.

Set Implicit Arguments.

(** Given a FRACTRAN program and a starting state, does it terminate *)

Definition FRACTRAN_PROBLEM := (list (nat*nat) * nat)%type.

Definition FRACTRAN_HALTING (P : FRACTRAN_PROBLEM) : Prop.
Proof.
  destruct P as (l & x).
  exact (l /F/ x ↓).
Defined.

(** Given a FRACTRAN program and a starting vector [v1,...,vn],
    does the program terminate starting from p1 * q1^v1 * ... qn^vn *)

Definition FRACTRAN_ALT_PROBLEM := (list (nat*nat) * { n : nat & vec nat n })%type.

Definition FRACTRAN_ALT_HALTING : FRACTRAN_ALT_PROBLEM -> Prop.
Proof.
  intros (l & n & v).
  exact (l /F/ ps 1 * exp 1 v ↓).
Defined.

Section MM_HALTING_FRACTRAN_ALT_HALTING.

  Let f : MM_PROBLEM -> FRACTRAN_ALT_PROBLEM.
  Proof.
    intros (n & P & v); red.
    destruct (mm_fractran_n P) as (l & H1 & _).
    split. 
    + exact l. 
    + exists n; exact v.
  Defined.

  Theorem MM_FRACTRAN_ALT_HALTING : MM_HALTING ⪯ FRACTRAN_ALT_HALTING.
  Proof.
    exists f; intros (n & P & v); simpl.
    destruct (mm_fractran_n P) as (l & H1 & H2); simpl; auto.
  Qed.

End MM_HALTING_FRACTRAN_ALT_HALTING.

Section FRACTRAN_ALT_HALTING_HALTING.

  Let f : FRACTRAN_ALT_PROBLEM -> FRACTRAN_PROBLEM.
  Proof.
    intros (l & n & v).
    exact (l,(ps 1 * exp 1 v)).
  Defined.

  Theorem FRACTRAN_ALT_HALTING_HALTING : FRACTRAN_ALT_HALTING ⪯ FRACTRAN_HALTING.
  Proof. 
    exists f; intros (n & P & v); simpl; tauto.
  Qed.

End FRACTRAN_ALT_HALTING_HALTING.

Corollary MM_FRACTRAN_HALTING : MM_HALTING ⪯ FRACTRAN_HALTING.
Proof.
  eapply reduces_transitive. apply MM_FRACTRAN_ALT_HALTING.
  exact FRACTRAN_ALT_HALTING_HALTING.
Qed.

Check MM_FRACTRAN_HALTING.
Print Assumptions MM_FRACTRAN_HALTING.
