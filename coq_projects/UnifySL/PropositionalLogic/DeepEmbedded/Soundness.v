Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Logic.MinimunLogic.Sound.Sound_Classical_Trivial.
Require Logic.MinimunLogic.Sound.Sound_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.
Require Logic.PropositionalLogic.Sound.Sound_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.ProofTheories.
Require Logic.PropositionalLogic.DeepEmbedded.TrivialSemantics.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Sound.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.
(*
Instance Intuitionistic_G: ProofTheory L := IntuitionisticLogic.G Var.
Instance DeMorgan_G: ProofTheory L := DeMorganLogic.G Var.
Instance GodelDummett_G: ProofTheory L := GodelDummettLogic.G Var.
Instance Classical_G: ProofTheory L := ClassicalLogic.G Var.
Instance Trivial_MD: Model := TrivialSemantics.MD Var.
Instance Trivial_SM: Semantics L Trivial_MD := TrivialSemantics.SM Var.
Instance Kripke_MD: Model := KripkeSemantics.MD Var.
Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
Instance Kripke_kpSM (M: Kmodel): KripkePropositionalSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kpSM Var M.
*)
Section Sound_Classical_Trivial.

Import Logic.MinimunLogic.Semantics.Trivial.
Import Logic.MinimunLogic.Sound.Sound_Classical_Trivial.
Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.

Existing Instances ProofTheories.ClassicalPropositionalLogic.minAX ProofTheories.ClassicalPropositionalLogic.ipG.
Existing Instances TrivialSemantics.MD TrivialSemantics.SM TrivialSemantics.tminSM TrivialSemantics.tpSM.

Theorem sound_classical_trivial: sound ProofTheories.ClassicalPropositionalLogic.G TrivialSemantics.SM (AllModel _).
Proof.
  hnf; intros.
  intro m.
  intros _.
  induction H.
  + pose proof sound_modus_ponens x y.
    exact (H1 m IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_excluded_middle.
Qed.

End Sound_Classical_Trivial.

Section Sound_Kripke.

Import Logic.MinimunLogic.Sound.Sound_Kripke.
Import Logic.PropositionalLogic.Sound.Sound_Kripke.
Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Existing Instances ProofTheories.IntuitionisticPropositionalLogic.minAX ProofTheories.IntuitionisticPropositionalLogic.ipG.
Existing Instances KripkeSemantics.MD KripkeSemantics.kMD KripkeSemantics.SM KripkeSemantics.kminSM KripkeSemantics.kpSM KripkeSemantics.R.

Theorem sound_intuitionistic_Kripke_all:
  sound ProofTheories.IntuitionisticPropositionalLogic.G KripkeSemantics.SM (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  hnf; intros.
  intros _ [M m [mono po_R]].
  pose proof (@KripkeSemantics.kiSM Sigma M mono po_R) as kiSM.
  hnf in mono, po_R.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
Qed.

Theorem sound_DeMorgan_Kripke_branch_join:
  sound ProofTheories.DeMorganPropositionalLogic.G KripkeSemantics.SM (KripkeModelClass _
    (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_BranchJoin)).
Proof.
  hnf; intros.
  intros _ [M m [[mono po_R] bkiM]].
  pose proof (@KripkeSemantics.kiSM Sigma M mono po_R) as kiSM.
  hnf in mono, po_R, bkiM.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_weak_excluded_middle_branch_join.
Qed.

Theorem sound_GodelDummett_Kripke_no_branch:
  sound ProofTheories.GodelDummettPropositionalLogic.G KripkeSemantics.SM (KripkeModelClass _
    (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_NoBranch)).
Proof.
  hnf; intros.
  intros _ [M m [[mono po_R] nkiM]].
  pose proof (@KripkeSemantics.kiSM Sigma M mono po_R) as kiSM.
  hnf in mono, po_R, nkiM.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_impp_choice_no_branch.
Qed.

Theorem sound_classical_Kripke_identity:
  sound ProofTheories.ClassicalPropositionalLogic.G KripkeSemantics.SM (KripkeModelClass _
    (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_Identity)).
Proof.
  hnf; intros.
  intros _ [M m [[mono po_R] ikiM]].
  pose proof (@KripkeSemantics.kiSM Sigma M mono po_R) as kiSM.
  hnf in mono, po_R, ikiM.
  induction H.
  + pose proof sound_modus_ponens x y m.
    exact (H1 IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_excluded_middle_ident.
Qed.

End Sound_Kripke.

End Sound.
