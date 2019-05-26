Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ShallowEmbedded.MonoPredicatePropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Sound.Sound_Flat.

Instance MonoPred_sL (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: SeparationLanguage (MonoPred_L A) :=
  Build_SeparationLanguage (MonoPred_L A) WeakSemanticsMono.sepcon WeakSemanticsMono.wand.

Instance MonoPred_s'L (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: SeparationEmpLanguage (MonoPred_L A) := 
  Build_SeparationEmpLanguage (MonoPred_L A) (MonoPred_sL A) WeakSemanticsMono.emp.

Instance MonoPred_fsSM  (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: @FlatSemantics.SeparatingSemantics (MonoPred_L A) (MonoPred_sL A) (Build_Model A) (unit_kMD _) tt R J (MonoPred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Qed.

Instance MonoPred_feSM (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {USA: UnitalSeparationAlgebra A}: @FlatSemantics.EmpSemantics (MonoPred_L A) (MonoPred_sL A) (MonoPred_s'L A) (Build_Model A) (unit_kMD _) tt R J (MonoPred_SM A).
Proof.
  apply Same_set_refl.
Qed.

Instance MonoPred_sGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A}: SeparationLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_sepcon_comm (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_fsSM A) x y).
  + intros x y.
    exact (@sound_sepcon_assoc (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_kpSM A) (MonoPred_fsSM A) x y).
  + intros x y z.
    exact (@sound_wand_sepcon_adjoint (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt  R po_R J (MonoPred_SM A) (MonoPred_kminSM A) (MonoPred_fsSM A) x y z).
Qed.

Instance MonoPred_EmpsGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {USA: UnitalSeparationAlgebra A}: EmpSeparationLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_sepcon_emp (MonoPred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_kpSM A) (MonoPred_fsSM A) _ (MonoPred_feSM A) _ x).
Qed.

Instance MonoPred_gcsGamma (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {J: Join A} {SA: SeparationAlgebra A} {uSA: UpwardsClosedSeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {incrSA: IncreasingSeparationAlgebra A}: GarbageCollectSeparationLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  intros.
  constructor.
  intros x y.
  exact (@sound_sepcon_elim1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD _) tt R J SA (MonoPred_SM A) (MonoPred_kiSM A) (MonoPred_kminSM A) (MonoPred_fsSM A) incrSA x y).
Qed.
