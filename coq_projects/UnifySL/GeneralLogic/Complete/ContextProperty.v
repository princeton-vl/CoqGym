Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.

Section ContextProperty.

Context {L: Language}.

Definition at_least (P cP: context -> Prop): Prop :=
  forall (Phi: context), cP Phi -> P Phi.

Lemma at_least_self: forall P, at_least P P.
Proof.
  intros.
  hnf; intros.
  auto.
Qed.

Lemma at_least_left: forall P cP1 cP2, at_least P cP1 -> at_least P (Intersection _ cP1 cP2).
Proof.
  intros.
  hnf in H |- *; intros.
  destruct H0; auto.
Qed.

Lemma at_least_right: forall P cP1 cP2, at_least P cP2 -> at_least P (Intersection _ cP1 cP2).
Proof.
  intros.
  hnf in H |- *; intros.
  destruct H0; auto.
Qed.

Definition maximal (P: context -> Prop): context -> Prop :=
  fun Phi => P Phi /\ forall Psi, P Psi -> Included _ Phi Psi -> Included _ Psi Phi.

Lemma sig_context_ext: forall (cP: context -> Prop) (Phi Psi: sig cP),
  (forall x, proj1_sig Phi x <-> proj1_sig Psi x) -> Phi = Psi.
Proof.
  intros.
  pose proof Extensionality_Ensembles _ _ _ (conj (fun x => proj1 (H x)) (fun x => proj2 (H x))).
  destruct Psi as [Psi ?], Phi as [Phi ?].
  simpl in H0; subst.
  pose proof proof_irrelevance _ c c0.
  subst.
  auto.
Qed.

End ContextProperty.

Ltac solve_at_least :=
  solve [apply at_least_self | auto | apply at_least_left; solve_at_least | apply at_least_right; solve_at_least].

