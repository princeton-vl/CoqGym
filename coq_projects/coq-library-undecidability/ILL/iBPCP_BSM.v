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
Require Import subcode sss. 
Require Import tiles_solvable bsm_defs bsm_pcp.

Fact tile_concat_itau ln lt : tile_concat ln lt = (itau1 lt (rev ln), itau2 lt (rev ln)).
Proof.
  induction ln as [ | i ln IH ]; simpl; auto.
  rewrite itau1_app, itau2_app; simpl.
  unfold card, string; generalize (nth i lt ([] / [])); intros (a,b); rewrite IH.
  repeat rewrite <- app_nil_end; auto.
Qed.

(* tiles_solvable & iBPCP is the same predicate except that the existentially
   quantified list is reversed *)

Theorem tiles_solvable_iBPCP lt : tiles_solvable lt <-> iBPCP lt.
Proof.
  split.
  + intros (ln & H1 & H2 & H3).
    rewrite tile_concat_itau in H3.
    exists (rev ln). 
    rewrite <- Forall_forall.
    repeat split; auto.
    * apply Forall_rev; auto.
    * contradict H1; rewrite <- (rev_involutive ln), H1; auto.
  + intros (ln & H1 & H2 & H3).
    exists (rev ln).
    rewrite tile_concat_itau, rev_involutive.
    repeat split; auto.
    * contradict H2; rewrite <- (rev_involutive ln), H2; auto.
    * apply Forall_rev, Forall_forall; auto.
Qed.

Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@bsm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@bsm_sss _) P s). 

Section iBPCP_BSM_HALTING.

  Let f (lt : list (card bool)) : BSM_PROBLEM.
  Proof.
    exists 4, 1, (pcp_bsm lt).
    exact (vec_set_pos (fun _ => nil)).
  Defined.

  Goal forall x, | pcp_bsm x| >= 80.
    intros; rewrite pcp_bsm_size; omega.
  Qed.
  
  Theorem iBPCP_BSM_HALTING : iBPCP ⪯ BSM_HALTING.
  Proof.
    exists f.
    intros lt.
    rewrite <- tiles_solvable_iBPCP.
    unfold BSM_HALTING; split.
    * intros H.
      apply pcp_bsm_sound with (v := vec_set_pos (fun _ => nil)) in H.
      match type of H with  _ // _ ->> (?q,?w) => exists (q, w) end.
      split; auto.
      simpl; omega.
    * intros ((q & w) & H).
      apply pcp_bsm_complete in H; tauto.
  Qed.

End iBPCP_BSM_HALTING.

