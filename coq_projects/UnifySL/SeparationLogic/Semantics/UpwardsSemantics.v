Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.StrongSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Class SeparatingSemantics
      (L: Language)
      {sL: SeparationLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      (SM: Semantics L MD): Type :=
{
  denote_sepcon: forall x y, Same_set _ (Kdenotation M (x * y)) (WeakSemantics.sepcon (Kdenotation M x) (Kdenotation M y));
  denote_wand: forall x y, Same_set _ (Kdenotation M (x -* y)) (StrongSemantics.wand (Kdenotation M x) (Kdenotation M y))
}.

Class EmpSemantics
      (L: Language)
      {sL: SeparationLanguage L}
      {s'L: SeparationEmpLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      (SM: Semantics L MD): Type :=
  denote_emp: Same_set _ (Kdenotation M emp) StrongSemantics.emp.

Lemma sat_sepcon
      {L: Language}
      {sL: SeparationLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      {SM: Semantics L MD}
      {usSM: SeparatingSemantics L MD M SM}:
  forall m x y,
    KRIPKE: M , m |= x * y <->
    exists m1 m2, join m1 m2 m /\
                  KRIPKE: M , m1 |= x /\
                  KRIPKE: M, m2 |= y.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_sepcon x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_wand
      {L: Language}
      {sL: SeparationLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      {SM: Semantics L MD}
      {usSM: SeparatingSemantics L MD M SM}:
  forall m x y,
    KRIPKE: M , m |= x -* y <->
    forall m0 m1 m2, m <= m0 ->
                     join m0 m1 m2 ->
                     KRIPKE: M , m1 |= x ->
                     KRIPKE: M, m2 |= y.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_wand x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_emp
      {L: Language}
      {sL: SeparationLanguage L}
      {s'L: SeparationEmpLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      {SM: Semantics L MD}
      {ueSM: EmpSemantics L MD M SM}:
  forall (m: Kworlds M), KRIPKE: M, m |= emp <-> increasing' m.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_emp.
  split; [apply H | apply H0].
Qed.
