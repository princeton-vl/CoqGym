Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.RelationPairs_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.StrongSemantics.
Require Import Logic.SeparationLogic.Sound.Sound_Flat.

Instance Pred_sL (A: Type) {J: Join A}: SeparationLanguage (Pred_L A) :=
  Build_SeparationLanguage (Pred_L A) WeakSemantics.sepcon WeakSemantics.wand.

Instance Pred_s'L (A: Type) {J: Join A}: SeparationEmpLanguage (Pred_L A) := 
  Build_SeparationEmpLanguage (Pred_L A) (Pred_sL A) (@WeakSemantics.emp _ eq J).

Instance Pred_fsSM (A: Type) {J: Join A}: @FlatSemantics.SeparatingSemantics (Pred_L A) (Pred_sL A) (Build_Model A) (unit_kMD _) tt eq J (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Qed.

Instance Pred_feSM (A: Type) {J: Join A}: @FlatSemantics.EmpSemantics (Pred_L A) (Pred_sL A) (Pred_s'L A) (Build_Model A) (unit_kMD _) tt eq J (Pred_SM A).
Proof.
  apply Same_set_refl.
Qed.

Instance Pred_sGamma (A: Type) {J: Join A} {SA: SeparationAlgebra A}: SeparationLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_sepcon_comm (Pred_L A) _ _ (Build_Model A) (unit_kMD _) tt eq J SA (Pred_SM A) (Pred_kminSM A) (Pred_fsSM A) x y).
  + intros x y.
    exact (@sound_sepcon_assoc (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA (Pred_SM A) (Pred_kminSM A) (Pred_kpSM A) (Pred_fsSM A) x y).
  + intros x y z.
    exact (@sound_wand_sepcon_adjoint (Pred_L A) _ _ (Build_Model A) (unit_kMD _) tt eq (eq_preorder _) J (Pred_SM A) (Pred_kminSM A) (Pred_fsSM A) x y z).
Qed.

Instance Pred_gcsGamma (A: Type) {J: Join A} {SA: SeparationAlgebra A} {incrSA: @IncreasingSeparationAlgebra A eq J}: GarbageCollectSeparationLogic (Pred_L A) (Pred_Gamma A).
Proof.
  intros.
  constructor.
  intros x y.
  exact (@sound_sepcon_elim1 (Pred_L A) _ _ (Build_Model A) (unit_kMD _) tt eq J SA (Pred_SM A) (Pred_kiSM A) (Pred_kminSM A) (Pred_fsSM A) incrSA x y).
Qed.

Instance Pred_EmpsGamma (A: Type) {J: Join A} {SA: SeparationAlgebra A} {USA: @UnitalSeparationAlgebra A eq J}: EmpSeparationLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_sepcon_emp (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA(Pred_SM A) (Pred_kiSM A) (Pred_kminSM A) (Pred_kpSM A) (Pred_fsSM A) _ (Pred_feSM A) USA x).
Qed.

