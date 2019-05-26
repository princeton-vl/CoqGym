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

Require Import ILL.Definitions.
Require Import bsm_defs mm_defs eill ill.

Require Import PCP_BPCP BPCP_iBPCP iBPCP_BSM BSM_MM MM_EILL EILL_ILL.

(** * List of all results *)

(** Reduction results for the following problems:

    0) PCP: Post Correspondence Problem 
    1) BPCP: Binary Post Correspondence Problem (see Definitions.v)
    2) BSM_HALTING: given a Binary Stack Machine P and an initial
       state st, starting at the first instruction of P with st
       as initial value for stacks, does the computation halt ?
       (see Bsm/bsm_defs.v)
    3) MM_HALTING: given a Minsky Machine P starting at instruction 1,
       and an initial state v (the initial values of registers), 
       does the computation starting from (1,v) reach the state (0,vec_zero) ?
       (see Mm/mm_defs.v)
    4) EILL_PROVABILITY: given an EILL sequent (elementary fragment of ILL)
       is it provable in G_EILL ? (see Ll/eill.v) 
    5) ILL_PROVABILITY: given a sequent of the (!,&,-o) fragment of ILL
       is it provable in G_ILL ? (see Ll/ill.v)
 *)

Check PCP_BPCP.                           Print Assumptions PCP_BPCP.
Check BPCP_iBPCP.                         Print Assumptions BPCP_iBPCP.
Check iBPCP_BSM_HALTING.                  Print Assumptions iBPCP_BSM_HALTING.
Check BSM_MM_HALTING.                     Print Assumptions BSM_MM_HALTING.
Check BSM_MM_HALTS_ON_ZERO.               Print Assumptions BSM_MM_HALTS_ON_ZERO.
Check MM_HALTS_ON_ZERO_EILL_PROVABILITY.  Print Assumptions MM_HALTS_ON_ZERO_EILL_PROVABILITY.
Check EILL_ILL_PROVABILITY.               Print Assumptions EILL_ILL_PROVABILITY.

Theorem PCP_BSM_HALTING : PCP ⪯ BSM_HALTING.
Proof.
  eapply reduces_transitive. exact PCP_BPCP.
  eapply reduces_transitive. exact BPCP_iBPCP.
  exact iBPCP_BSM_HALTING.
Qed.

Theorem PCP_MM_HALTS_ON_ZERO : PCP ⪯ MM_HALTS_ON_ZERO.
Proof.
  eapply reduces_transitive. exact PCP_BSM_HALTING.
  exact BSM_MM_HALTS_ON_ZERO.
Qed.

Theorem PCP_MM_HALTING : PCP ⪯ MM_HALTING.
Proof.
  eapply reduces_transitive. exact PCP_BSM_HALTING.
  exact BSM_MM_HALTING.
Qed.

Theorem PCP_ILL : PCP ⪯ ILL_PROVABILITY.
Proof.
  eapply reduces_transitive. exact PCP_MM_HALTS_ON_ZERO.
  eapply reduces_transitive. exact MM_HALTS_ON_ZERO_EILL_PROVABILITY.
  exact EILL_ILL_PROVABILITY.
Qed.

(** * Formal Undecidability *)

Module Def_of_undec.

  Inductive dec {X} (P : X -> Prop) : Prop := is_dec (H : forall x, { P x} + {~ P x}).

  Notation compl P := (fun x => ~ P x).

  Notation "Q ⪯T P" := (dec (P) -> dec (Q)) (at level 20).

  Lemma red_turing X Y (P : X -> Prop) (Q : Y -> Prop) : P ⪯ Q -> P ⪯T Q.
  Proof.
    intros (f & Hf) [ H ].
    exists.
    intros x; destruct (H (f x)) as [ H1 | H1 ]; 
      rewrite <- Hf in H1; tauto.
  Qed.

  (* Lemma red_turing_compl X Y (Q : Y -> Prop) (P : X -> Prop) : *)
  (*   Q ⪯ P -> compl Q ⪯T compl P. *)
  (* Proof. *)
  (*   intros [f] [d]. econstructor. intros x. *)
  (*   destruct (d (f x)). *)
  (*   + left. firstorder. *)
  (*   + right. firstorder. *)
  (* Qed. *)
  
  Inductive undec : forall X, (X -> Prop) -> Prop :=
    undec_seed : undec PCP
  | undec_red X (P : X -> Prop) Y (Q : Y -> Prop) : Q ⪯T P -> undec Q -> undec P.

  Lemma red_undec  X Y (Q : Y -> Prop) (P : X -> Prop) :
    Q ⪯ P -> undec Q -> undec P.
  Proof.
    intros. eapply undec_red. eapply red_turing; eauto. eauto.
  Qed.
    
  Lemma undec_compl X (P : X -> Prop) :
    undec (compl P) -> undec P.
  Proof.
    intros. eapply undec_red; try eassumption. firstorder.
  Qed.
  
  Lemma undec_PCP X (P : X -> Prop) :
    undec P <-> (PCP ⪯T P).
  Proof.
    split; intros.
    - induction H; eauto.
    - eauto using undec. 
  Qed.
    
End Def_of_undec.
