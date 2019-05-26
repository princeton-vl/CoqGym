Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Logic.MinimunLogic.Sound.Sound_Kripke.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLanguage.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLogic.
Require Logic.MinimunLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

(* TODO: soundness about trivial semantics is not yet added. *)

Section Sound.

Context (Var: Type).

Instance L: Language := MinimunLanguage.L Var.
Instance minL: MinimunLanguage L := MinimunLanguage.minL Var.

Instance G: ProofTheory L := MinimunLogic.G Var.
Instance AX: NormalAxiomatization L G := MinimunLogic.AX Var.
Instance minAX: MinimunAxiomatization L G := MinimunLogic.minAX Var.

Instance Kripke_MD: Model := KripkeSemantics.MD Var.
Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
Instance Kripke_kminSM (M: Kmodel): KripkeMinimunSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kminSM Var M.

Section Sound_Kripke.

Import Logic.MinimunLogic.Sound.Sound_Kripke.
Import Logic.MinimunLogic.DeepEmbedded.KripkeSemantics.

Theorem sound_intuitionistic_Kripke_all:
  sound G Kripke_SM (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  hnf; intros.
  intros _ [M m [mono po_R]].
  pose proof (@KripkeSemantics.kiSM Var M mono po_R) as kiSM.
  hnf in mono, po_R.
  change (Kmodel Var) in M.
  change (Kworlds M) in m.
  change (KRIPKE: M, m |= x).
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
Qed.

End Sound_Kripke.

End Sound.
