Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Sound.Sound_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Sound.Sound_Kripke.

Instance MonoPred_minL (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: MinimunLanguage (MonoPred_L A) := Build_MinimunLanguage (MonoPred_L A) SemanticsMono.impp.
Instance MonoPred_pL (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: PropositionalLanguage (MonoPred_L A) := Build_PropositionalLanguage (MonoPred_L A) SemanticsMono.andp SemanticsMono.orp SemanticsMono.falsep.

Instance MonoPred_kiSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeIntuitionisticSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  intros; apply (proj2_sig _).
Qed.

Instance MonoPred_kminSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkeMinimunSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

Instance MonoPred_kpSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: KripkePropositionalSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + apply Same_set_refl.
Qed.

Instance MonoPred_Gamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: ProofTheory (MonoPred_L A) := Build_AxiomaticProofTheory (fun x: expr => forall a: A, proj1_sig x a).

Instance MonoPred_nGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: NormalAxiomatization (MonoPred_L A) (MonoPred_Gamma A) := Build_AxiomaticProofTheory_AX (fun x: expr => forall a: A, proj1_sig x a).

Instance MonoPred_minAX (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: MinimunAxiomatization (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y ? ? m.
    pose proof @sound_modus_ponens (MonoPred_L A) _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kminSM A) x y.
    exact (H1 m (H m) (H0 m)).
  + intros x y.
    exact (@sound_axiom1 (MonoPred_L A) _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) x y).
  + intros x y z.
    exact (@sound_axiom2 (MonoPred_L A) _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kminSM A) x y z).
Qed.

Instance MonoPred_ipGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation}: IntuitionisticPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_andp_intros (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x y).
  + intros x y.
    exact (@sound_andp_elim1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x y).
  + intros x y.
    exact (@sound_andp_elim2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x y).
  + intros x y.
    exact (@sound_orp_intros1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x y).
  + intros x y.
    exact (@sound_orp_intros2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x y).
  + intros x y z.
    exact (@sound_orp_elim (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x y z).
  + intros x.
    exact (@sound_falsep_elim (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) x).
Qed.

Instance MonoPred_gdpGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {nkiM: NoBranchKripkeIntuitionisticModel A}: GodelDummettPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x y.
  exact (@sound_impp_choice_no_branch (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_kpSM A) nkiM x y).
Qed.

Instance MonoPred_dmpGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {bkiM: BranchJoinKripkeIntuitionisticModel A}: DeMorganPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_weak_excluded_middle_branch_join (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R po_R (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_kpSM A) bkiM x).
Qed.

Instance MonoPred_cpGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {ikiM: IdentityKripkeIntuitionisticModel A}: ClassicalPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_excluded_middle_ident (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) ikiM x).
Qed.
