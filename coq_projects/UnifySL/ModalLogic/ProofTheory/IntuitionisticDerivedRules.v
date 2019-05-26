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

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Section IntuitionisticDerivedRules.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {KmGamma: SystemK L Gamma}.

Lemma boxp_andp: forall x y, |-- boxp (x && y) <--> (boxp x && boxp y).
Proof.
  intros.
  apply solve_andp_intros.
  + rewrite <- (andp_elim1 x y) at 2.
    rewrite <- (andp_elim2 x y) at 3.
    rewrite andp_dup.
    apply provable_impp_refl.
  + rewrite <- impp_curry_uncurry.
    rewrite <- axiom_K.
    rewrite <- axiom_K.
    apply rule_N.
    apply andp_intros.
Qed.

Lemma orp_boxp: forall x y, |-- boxp x || boxp y --> boxp (x || y).
Proof.
  intros.
  apply solve_orp_impp.
  + rewrite <- axiom_K.
    apply rule_N.
    apply orp_intros1.
  + rewrite <- axiom_K.
    apply rule_N.
    apply orp_intros2.
Qed.

Lemma boxp_TT: |-- boxp TT.
Proof.
  apply rule_N.
  apply provable_impp_refl.
Qed.

Lemma not_diamondp_FF: |-- ~~ diamondp FF.
Proof.
  intros.
  unfold diamondp.
  rewrite <- double_negp_intros.
  apply rule_N.
  apply provable_impp_refl.
Qed.

Lemma impp_diamondp: forall x y, |-- boxp (x --> y) --> (diamondp x --> diamondp y).
Proof.
  intros.
  unfold diamondp.
  rewrite <- contrapositivePP.
  rewrite <- axiom_K.
  rewrite <- axiom_K.
  apply rule_N.
  apply contrapositivePP.
Qed.
(*
Lemma derivable_impp_diamondp: forall Phi x y, Phi |-- boxp (x --> y) --> (diamondp x --> diamondp y).
Proof.
  intros.
  apply deduction_weaken0.
  apply impp_diamondp.
Qed.

Lemma deduction_impp_diamondp: forall Phi x y,
  Phi |-- boxp (x --> y) ->
  Phi |-- (diamondp x --> diamondp y).
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_impp_diamondp.
Qed.
*)
Lemma diamondp_andp: forall x y, |-- diamondp (x && y) --> (diamondp x && diamondp y).
Proof.
  intros.
  apply solve_impp_andp.
  + rewrite <- impp_diamondp.
    apply rule_N.
    apply andp_elim1.
  + rewrite <- impp_diamondp.
    apply rule_N.
    apply andp_elim2.
Qed.

Lemma orp_diamondp: forall x y, |-- diamondp x || diamondp y --> diamondp (x || y).
Proof.
  intros.
  apply solve_orp_impp.
  + rewrite <- impp_diamondp.
    apply rule_N.
    apply orp_intros1.
  + rewrite <- impp_diamondp.
    apply rule_N.
    apply orp_intros2.
Qed.

Lemma P_diamondp_P {TmGamma: SystemT L Gamma}: forall x, |-- x --> diamondp x.
Proof.
  intros.
  unfold diamondp.
  rewrite <- contrapositivePN.
  apply axiom_T.
Qed.

End IntuitionisticDerivedRules.
