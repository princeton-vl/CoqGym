Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Semantics.Kripke.
Require Import Logic.ModalLogic.Sound.Sound_Kripke.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.

Instance Pred_mL (A: Type) {R: KM.Relation A}: ModalLanguage (Pred_L A) :=
  Build_ModalLanguage (Pred_L A) Semantics.boxp.

Instance Pred_kmSM (A: Type) {R: KM.Relation A}: @KripkeModalSemantics (Pred_L A) (Pred_minL A) (Pred_mL A) (Build_Model A) (unit_kMD _) tt R (Pred_SM A).
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

Instance Pred_KmGamma (A: Type) {R: KM.Relation A}: SystemK (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_axiom_K (Pred_L A) _ _ (Build_Model A) (unit_kMD _) tt R (Pred_SM A) (Pred_tminSM A) (Pred_kmSM A) x y).
  + intros x.
    exact (@sound_rule_N (Pred_L A) _ _ (Build_Model A) (unit_kMD _) tt R (Pred_SM A) (Pred_kmSM A) x).
Qed.
