Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.

Local Open Scope logic_base.
Local Open Scope syntax.

Section RewriteClass.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}.

Instance provable_impp_rewrite: RewriteRelation (fun x y => |-- x --> y).

Instance provable_impp_refl {minAX: MinimunAxiomatization L Gamma}: Reflexive (fun x y => |-- x --> y).
Proof.
  intros.
  hnf; intros.
  apply provable_impp_refl.
Qed.

Instance provable_proper_impp {minAX: MinimunAxiomatization L Gamma} : Proper ((fun x y => |-- impp x y) ==> Basics.impl) provable.
Proof.
  intros.
  hnf; intros.
  intro.
  eapply modus_ponens; eauto.
Qed.

Instance impp_proper_impp {minAX: MinimunAxiomatization L Gamma} : Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) impp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  eapply aux_minimun_rule02; [apply H |].
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  apply aux_minimun_rule01, H0.
Qed.

Instance derivable_proper_impp {SC: NormalSequentCalculus L Gamma} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimunSequentCalculus L Gamma} : Proper (eq ==> (fun x y => |-- impp x y) ==> Basics.impl) derivable.
Proof.
  hnf; intros Phi Phi' ?; subst Phi'.
  hnf; intros x1 x2 ?.
  intro.
  apply (deduction_weaken0 Phi) in H.
  exact (deduction_modus_ponens _ _ _ H0 H).
Qed.

End RewriteClass.

Existing Instances provable_impp_rewrite
                   provable_impp_refl
                   provable_proper_impp
                   derivable_proper_impp
                   impp_proper_impp.

Module TestInAxiomatization.

Section TestInAxiomatization.

(* Here, "Section" is used to avoid leaking "Existing Instances". *)

Existing Instances Axiomatization2SequentCalculus_SC
                   Axiomatization2SequentCalculus_bSC
                   Axiomatization2SequentCalculus_minSC.

Goal forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {AX: NormalAxiomatization L Gamma} {minAX: MinimunAxiomatization L Gamma} (Phi: context) y1 y2,
  |-- y1 --> y2 ->
  Phi |-- y1 ->
  Phi |-- y2.
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {AX: NormalAxiomatization L Gamma} {minAX: MinimunAxiomatization L Gamma} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  Phi |-- x1 --> y1 ->
  Phi |-- x2 --> y2.
Proof.
  intros.
  rewrite H0 in H1.
  rewrite H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {AX: NormalAxiomatization L Gamma} {minAX: MinimunAxiomatization L Gamma} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  |-- (x1 --> y1) --> (x2 --> y2).
Proof.
  intros.
  rewrite <- H0, H.
  apply provable_impp_refl.
Qed.

End TestInAxiomatization.

End TestInAxiomatization.

Module TestInSequentCalculus.

Section TestInSequentCalculus.

(* Here, "Section" is used to avoid leaking "Existing Instances". *)

Existing Instances SequentCalculus2Axiomatization_minAX.

Goal forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {SC: NormalSequentCalculus L Gamma} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimunSequentCalculus L Gamma} (Phi: context) y1 y2,
  |-- y1 --> y2 ->
  Phi |-- y1 ->
  Phi |-- y2.
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {SC: NormalSequentCalculus L Gamma} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimunSequentCalculus L Gamma} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  Phi |-- x1 --> y1 ->
  Phi |-- x2 --> y2.
Proof.
  intros.
  rewrite H0 in H1.
  rewrite H.
  auto.
Qed.

Goal forall {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {SC: NormalSequentCalculus L Gamma} {bSC: BasicSequentCalculus L Gamma} {minSC: MinimunSequentCalculus L Gamma} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  |-- (x1 --> y1) --> (x2 --> y2).
Proof.
  intros.
  rewrite <- H0, H.
  apply provable_impp_refl.
Qed.

End TestInSequentCalculus.

End TestInSequentCalculus.
