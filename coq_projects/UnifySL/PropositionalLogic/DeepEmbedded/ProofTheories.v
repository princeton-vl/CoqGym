Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Module IntuitionisticPropositionalLogic.

Section IntuitionisticPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x).

Instance G: ProofTheory PropositionalLanguage.L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization PropositionalLanguage.L G := Build_AxiomaticProofTheory_AX provable.

Instance minAX: MinimunAxiomatization PropositionalLanguage.L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

End IntuitionisticPropositionalLogic.

End IntuitionisticPropositionalLogic.

Module DeMorganPropositionalLogic.

Section DeMorganPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| weak_excluded_middle: forall x, provable (~~ x || ~~ ~~ x).

Instance G: ProofTheory PropositionalLanguage.L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization PropositionalLanguage.L G := Build_AxiomaticProofTheory_AX provable.

Instance minAX: MinimunAxiomatization PropositionalLanguage.L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance dmpG: DeMorganPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  apply weak_excluded_middle.
Qed.

End DeMorganPropositionalLogic.

End DeMorganPropositionalLogic.

Module GodelDummettPropositionalLogic.

Section GodelDummettPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| impp_choice: forall x y, provable ((x --> y) || (y --> x)).

Instance G: ProofTheory PropositionalLanguage.L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization PropositionalLanguage.L G := Build_AxiomaticProofTheory_AX provable.

Instance minAX: MinimunAxiomatization PropositionalLanguage.L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance gdpG: GodelDummettPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  apply impp_choice.
Qed.

Instance dmpG: DeMorganPropositionalLogic PropositionalLanguage.L G.
Proof.
  apply GodelDummett2DeMorgan.
Qed.

End GodelDummettPropositionalLogic.

End GodelDummettPropositionalLogic.

Module ClassicalPropositionalLogic.

Section ClassicalPropositionalLogic.

Context {Sigma: PropositionalLanguage.PropositionalVariables}.

Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| excluded_middle: forall x, provable (x || (x --> FF)).

Instance G: ProofTheory PropositionalLanguage.L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization PropositionalLanguage.L G := Build_AxiomaticProofTheory_AX provable.

Instance minAX: MinimunAxiomatization PropositionalLanguage.L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance cpG: ClassicalPropositionalLogic PropositionalLanguage.L G.
Proof.
  constructor.
  apply excluded_middle.
Qed.

Instance gdpG: GodelDummettPropositionalLogic PropositionalLanguage.L G.
Proof.
  apply Classical2GodelDummett.
Qed.

Instance dmpG: DeMorganPropositionalLogic PropositionalLanguage.L G.
Proof.
  apply GodelDummett2DeMorgan.
Qed.

End ClassicalPropositionalLogic.

End ClassicalPropositionalLogic.





