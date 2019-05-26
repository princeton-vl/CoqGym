Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Definitions.

Require Import Logic.ChoiceFacts.

Section first_order.

Context `{Tn:Tarski_neutral_dimensionless}.

(** Dedekind's axiom of continuity implies the Tarski's axiom schema of continuity *)

Lemma dedekind__fod : dedekind_s_axiom -> first_order_dedekind.
Proof.
  intros dedekind Alpha Beta HAlpha HBeta HA.
  apply dedekind, HA.
Qed.

(** This is a type whose members describe first-order formulas *)

Inductive tFOF :=
  eq_fof1 : Tpoint -> Tpoint -> tFOF
| bet_fof1 : Tpoint -> Tpoint -> Tpoint -> tFOF
| cong_fof1 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> tFOF
| not_fof1 : tFOF -> tFOF
| and_fof1 : tFOF -> tFOF -> tFOF
| or_fof1 : tFOF -> tFOF -> tFOF
| implies_fof1 : tFOF -> tFOF -> tFOF
| forall_fof1 : (Tpoint -> tFOF) -> tFOF
| exists_fof1 : (Tpoint -> tFOF) -> tFOF.

(** This function interperts tFOF elements as Prop *)

Fixpoint fof1_prop (F:tFOF) := match F with
  eq_fof1 A B => A = B
| bet_fof1 A B C => Bet A B C
| cong_fof1 A B C D => Cong A B C D
| not_fof1 F1 => ~ fof1_prop F1
| and_fof1 F1 F2 => fof1_prop F1 /\ fof1_prop F2
| or_fof1 F1 F2 => fof1_prop F1 \/ fof1_prop F2
| implies_fof1 F1 F2 => fof1_prop F1 -> fof1_prop F2
| forall_fof1 P => forall A, fof1_prop (P A)
| exists_fof1 P => exists A, fof1_prop (P A) end.

(** Every first-order formula is equivalent to a Prop built with fof1_prop *)

Lemma fof__fof1 : FunctionalChoice_on Tpoint tFOF ->
  forall F, FOF F -> exists F1,  F <-> fof1_prop F1 .
Proof.
  intros choice F HFOF.
  induction HFOF.
  - exists (eq_fof1 A B); intuition.
  - exists (bet_fof1 A B C); intuition.
  - exists (cong_fof1 A B C D); intuition.
  - destruct IHHFOF as [F1]. exists (not_fof1 F1). simpl; intuition.
  - destruct IHHFOF1 as [F1]; destruct IHHFOF2 as [F2]; exists (and_fof1 F1 F2); simpl; intuition.
  - destruct IHHFOF1 as [F1]; destruct IHHFOF2 as [F2]; exists (or_fof1 F1 F2); simpl; intuition.
  - destruct IHHFOF1 as [F1]; destruct IHHFOF2 as [F2]; exists (implies_fof1 F1 F2); simpl; intuition.
  - destruct (choice (fun A => (fun F1 => P A <-> fof1_prop F1)) H0) as [f].
    exists (forall_fof1 f); simpl.
    split; intros HH A; apply H1, HH.
  - destruct (choice (fun A => (fun F1 => P A <-> fof1_prop F1)) H0) as [f].
    exists (exists_fof1 f); simpl.
    split; intros [A HA]; exists A; apply H1, HA.
Qed.

(** Every Prop built with fof1_prop is a first-order formula *)

Lemma fof1__fof : forall F1, FOF (fof1_prop F1).
Proof.
  induction F1; constructor; assumption.
Qed.

End first_order.