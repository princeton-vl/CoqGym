Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.IntuitionisticDerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Section ClassicalderivedRules.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {KmGamma: SystemK L Gamma}.

Existing Instances Classical2GodelDummett GodelDummett2DeMorgan.

Lemma diamondp_orp: forall x y, |-- diamondp (x || y) <--> (diamondp x || diamondp y).
Proof.
  intros.
  apply solve_andp_intros; [| apply orp_diamondp].
  unfold diamondp.
  rewrite <- demorgan_negp_andp.
  rewrite <- contrapositivePP.
  rewrite <- boxp_andp.
  rewrite demorgan_negp_orp.
  apply provable_impp_refl.
Qed.

Instance PropositionalTransparentModality2StrongPropositionalTransparentModality {pmGamma: PropositionalTransparentModality L Gamma}: StrongPropositionalTransparentModality L Gamma.
Proof.
  constructor.
  intros.
  apply solve_andp_intros; [apply axiom_K |].
  rewrite (impp2orp x y), (impp2orp (boxp x) (boxp y)).
  rewrite boxp_orp.
  apply solve_orp_impp; [| apply orp_intros2].
  rewrite <- orp_intros1.
  apply (modus_ponens (boxp (x || ~~ x))).
  + rewrite boxp_orp.
    apply solve_orp_impp; [| apply axiom1].
    clear KmGamma pmGamma; AddSequentCalculus Gamma.
    rewrite provable_derivable.
    rewrite <- !deduction_theorem.
    apply deduction_falsep_elim.
    apply deduction_modus_ponens with (boxp x); solve_assum.
  + apply rule_N.
    apply excluded_middle.
Qed.

End ClassicalderivedRules.
