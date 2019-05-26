Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.ModalLogic.Semantics.Flat.
Require Import Logic.ModalLogic.Sound.Sound_Flat.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.

Instance MonoPred_mL (A: Type) {R1: KI.Relation A} {po_R1: PreOrder KI.Krelation} {R2: KM.Relation A} {uR2: UpwardsClosedOrderedKripkeModel A} : ModalLanguage (MonoPred_L A) :=
  Build_ModalLanguage (MonoPred_L A) SemanticsMono.boxp.

Instance MonoPred_fmSM (A: Type) {R1: KI.Relation A} {po_R1: PreOrder KI.Krelation} {R2: KM.Relation A} {uR2: UpwardsClosedOrderedKripkeModel A} : @FlatModalSemantics (MonoPred_L A) (MonoPred_minL A) (MonoPred_mL A) (Build_Model A) (unit_kMD _) tt R1 R2 (MonoPred_SM A).
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

Instance MonoPred_KmGamma (A: Type) {R1: KI.Relation A} {po_R1: PreOrder KI.Krelation} {R2: KM.Relation A} {uR2: UpwardsClosedOrderedKripkeModel A}: SystemK (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_axiom_K (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 R2 _ (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_fmSM A) x y).
  + intros x.
    exact (@sound_rule_N (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R1 R2 (MonoPred_SM A) (MonoPred_fmSM A) x).
Qed.

Instance MonoPred_pmGamma (A: Type) {R1: KI.Relation A} {po_R1: PreOrder KI.Krelation} {R2: KM.Relation A} {uR2: UpwardsClosedOrderedKripkeModel A} {pf_R2: PartialFunctional KM.Krelation}: PropositionalTransparentModality (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x y.
  exact (@sound_boxp_orp (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R1 R2 (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) (MonoPred_fmSM A) pf_R2 x y).
Qed.
