Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class DeMorganPropositionalLogic (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {minAX: MinimunAxiomatization L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  weak_excluded_middle: forall x, |-- ~~ x || ~~ ~~ x
}.

Lemma MakeSequentCalculus_DeMorganPropositionalLogic {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {minAX: MinimunAxiomatization L Gamma} (minAX': MinimunAxiomatization L (Build_AxiomaticProofTheory (@provable L Gamma))) (ipGamma: IntuitionisticPropositionalLogic L Gamma) {ipGamma': IntuitionisticPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))} {dmpGamma: DeMorganPropositionalLogic L Gamma}:
  Typeclass_Rewrite (exist (fun X: Prop => X) (IntuitionisticPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))) ipGamma' :: nil) ->
  forall (G: Prop) (l: list (sig (fun X: Prop => X))),
  (forall
     (dmpGamma: DeMorganPropositionalLogic L (Build_AxiomaticProofTheory (@provable L Gamma))),
     OpaqueProp (Typeclass_Rewrite l -> G)) <->
  OpaqueProp (Typeclass_Rewrite ((exist (fun X: Prop => X) (DeMorganPropositionalLogic L Gamma) dmpGamma) :: l) -> G).
Proof.
  unfold OpaqueProp.
  intros _.
  intros.
  split; intros.
  + clear H0.
    apply H; auto.
    - destruct dmpGamma; constructor; auto.
    - apply Typeclass_Rewrite_I.
  + apply H; auto.
    apply Typeclass_Rewrite_I.
Qed.

Hint Rewrite <- @MakeSequentCalculus_DeMorganPropositionalLogic using (instantiate (1 := _); apply Typeclass_Rewrite_I): AddSC.

Section DeMorgan.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {dmpGamma: DeMorganPropositionalLogic L Gamma}.
(*
Lemma derivable_weak_excluded_middle: forall (Phi: context) (x: expr),
  Phi |-- ~~ x || ~~ ~~ x.
Proof.
  intros.
  pose proof weak_excluded_middle x.
  apply deduction_weaken0; auto.
Qed.
*)
Lemma demorgan_negp_andp: forall (x y: expr),
  |-- ~~ (x && y) <--> (~~ x || ~~ y).
Proof.
  AddSequentCalculus Gamma.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros; [| rewrite <- provable_derivable; apply demorgan_orp_negp].
  rewrite <- deduction_theorem.
  apply (deduction_modus_ponens _ (~~ x || ~~ ~~ x)); [apply deduction_weaken0, weak_excluded_middle |].
  apply deduction_orp_elim'.
  + apply deduction_weaken0.
    apply orp_intros1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    unfold negp at 4.
    rewrite <- deduction_theorem.
    apply (deduction_modus_ponens _ (x --> FF)).
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ (x && y)).
      * apply deduction_andp_intros; [| apply deduction_weaken1]; apply derivable_assum1.
      * do 3 apply deduction_weaken1; apply derivable_assum1.
    - apply deduction_weaken1; apply derivable_assum1.
Qed.

End DeMorgan.
