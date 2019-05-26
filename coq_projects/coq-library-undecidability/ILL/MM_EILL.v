(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Omega.

Require Import ILL.Definitions.

Require Import utils pos vec. 
Require Import subcode sss mm_defs.
Require Import eill eill_mm.

Local Notation "P '/MM/' s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P '/MM/' s ~~> t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).

Section MM_HALTING_EILL_PROVABILITY.

  Let f : MM_PROBLEM -> EILL_SEQUENT.
  Proof.
    intros (n & P & v).
    exact (Sig (1,P) 0, vec_map_list v (fun p : pos n => pos2nat p), 2 * n + 1).
  Defined.

  Theorem MM_HALTS_ON_ZERO_EILL_PROVABILITY : MM_HALTS_ON_ZERO ⪯ EILL_PROVABILITY.
  Proof.
    exists f.
    intros (n & P & v); simpl.
    rewrite <- G_eill_mm; simpl; auto.
    split.
    + intros (? & _); auto.
    + split; simpl; auto.
  Qed.

End MM_HALTING_EILL_PROVABILITY.
