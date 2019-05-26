Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.

Section MinimunLogic.

Context (Var: Type).

Instance L: Language := MinimunLanguage.L Var.
Instance minL: MinimunLanguage L := MinimunLanguage.minL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization L G := Build_AxiomaticProofTheory_AX provable.

Instance minAX: MinimunAxiomatization L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance SC: NormalSequentCalculus L G := Axiomatization2SequentCalculus_SC.

Instance bSC: BasicSequentCalculus L G := Axiomatization2SequentCalculus_bSC.

Instance fwSC: FiniteWitnessedSequentCalculus L G := Axiomatization2SequentCalculus_fwSC.

Instance minSC: MinimunSequentCalculus L G := Axiomatization2SequentCalculus_minSC.

End MinimunLogic.
