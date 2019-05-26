Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bisimulation.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Semantics.SemanticStable.
Require Logic.PropositionalLogic.Semantics.Trivial.
Require Logic.ModalLogic.Semantics.Kripke.
Require Logic.GeneralLogic.Semantics.Kripke.
Require Logic.MinimunLogic.Semantics.Kripke.
Require Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.ModalLogic.Semantics.Flat.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Logic.SeparationLogic.Semantics.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Sound_Trivial.

Import Logic.PropositionalLogic.Semantics.Trivial.
Import Logic.MinimunLogic.Semantics.Trivial.
Import Logic.ModalLogic.Semantics.Kripke.

Lemma sound_impp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {tminSM: TrivialMinimunSemantics L MD SM} {tpSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x --> y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  unfold Kdenotation in *; simpl in *.
  rewrite !(app_same_set (denote_impp _ _)).
  unfold Semantics.impp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_andp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x && y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  unfold Kdenotation in *; simpl in *.
  rewrite !(app_same_set (denote_andp _ _)).
  unfold Semantics.andp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_orp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x || y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  unfold Kdenotation in *; simpl in *.
  rewrite !(app_same_set (denote_orp _ _)).
  unfold Semantics.orp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_falsep_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  semantic_stable falsep.
Proof.
  intros.
  rewrite denote_stable.
  unfold Semantics.stable.
  intros.
  unfold Kdenotation.
  rewrite !(app_same_set denote_falsep).
  reflexivity.
Qed.

Lemma sound_stable_proper_iffp {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {tminSM: TrivialMinimunSemantics L MD SM} {tpSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y,
    (forall m, KRIPKE: M, m |= x <--> y) ->
    (semantic_stable x <-> semantic_stable y).
Proof.
  intros.
  rewrite !denote_stable.
  unfold Semantics.stable.
  assert (forall m, Kdenotation M x m <-> Kdenotation M y m).
  + intros m.
    specialize (H m).
    unfold iffp in H; rewrite sat_andp, !sat_impp in H.
    destruct H.
    tauto.
  + split; intros HH ? ? H1;
    specialize (HH _ _ H1).
    - rewrite !H0 in HH.
      auto.
    - rewrite !H0.
      auto.
Qed.

Lemma sound_boxp_stable {L: Language} {minL: MinimunLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KM.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {R1_bis: Bisimulation SS.Krelation KM.Krelation} {SM: Semantics L MD} {kmSM: KripkeModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x -> semantic_stable (boxp x).
Proof.
  intros.
  rewrite denote_stable in H |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_boxp _)).
  unfold Semantics.boxp; simpl.
  split.
  + pose proof bis_r _ _ H0.
    intros.
    specialize (H1 _ H3).
    destruct H1 as [m0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
  + pose proof bis_l _ _ H0.
    intros; rename n0 into m0.
    specialize (H1 _ H3).
    destruct H1 as [n0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
Qed.

Lemma sound_boxp_absorb_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KM.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {R1_incl: Inclusion KM.Krelation SS.Krelation} {SM: Semantics L MD} {tminSM: TrivialMinimunSemantics L MD SM} {tpSM: TrivialPropositionalSemantics L MD SM} {kmSM: KripkeModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x ->
    (forall (m: Kworlds M), KRIPKE: M, m |= x --> boxp x).
Proof.
  intros.
  rewrite sat_impp, sat_boxp.
  intros.
  rewrite denote_stable in H.
  unfold Semantics.stable in H.
  apply including in H1.
  specialize (H _ _ H1).
  tauto.
Qed.

End Sound_Trivial.

Module Sound_KripkeIntuitionistic.

Import Logic.GeneralLogic.Semantics.Kripke.
Import Logic.MinimunLogic.Semantics.Kripke.
Import Logic.PropositionalLogic.Semantics.Kripke.
Import Logic.ModalLogic.Semantics.Flat.
Import Logic.SeparationLogic.Semantics.FlatSemantics.

Lemma sound_impp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {R1_bis: Bisimulation SS.Krelation KI.Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x --> y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_impp _ _)).
  unfold Semantics.impp; simpl.
  split.
  + pose proof bis_r _ _ H1.
    intros.
    specialize (H2 _ H4).
    destruct H2 as [m0 [? ?]].
    specialize (H3 _ H2).
    specialize (H _ _ H6).
    specialize (H0 _ _ H6).
    tauto.
  + pose proof bis_l _ _ H1.
    intros.
    rename n0 into m0.
    specialize (H2 _ H4).
    destruct H2 as [n0 [? ?]].
    specialize (H3 _ H2).
    specialize (H _ _ H6).
    specialize (H0 _ _ H6).
    tauto.
Qed.

Lemma sound_andp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x && y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_andp _ _)).
  unfold Semantics.andp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_orp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x || y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_orp _ _)).
  unfold Semantics.orp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_falsep_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  semantic_stable falsep.
Proof.
  intros.
  rewrite denote_stable.
  unfold Semantics.stable.
  intros.
  rewrite !(app_same_set denote_falsep).
  reflexivity.
Qed.

Lemma sound_stable_proper_iffp {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {po_R: PreOrder KI.Krelation} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y,
    (forall m, KRIPKE: M, m |= x <--> y) ->
    (semantic_stable x <-> semantic_stable y).
Proof.
  intros.
  rewrite !denote_stable.
  unfold Semantics.stable.
  assert (forall m, Kdenotation M x m <-> Kdenotation M y m).
  + intros m.
    specialize (H m).
    unfold iffp in H; rewrite sat_andp, !sat_impp in H.
    destruct H.
    split; intros.
    - apply (H m); auto.
      reflexivity.
    - apply (H0 m); auto.
      reflexivity.
  + split; intros HH ? ? H1;
    specialize (HH _ _ H1).
    - rewrite !H0 in HH.
      auto.
    - rewrite !H0.
      auto.
Qed.

Lemma sound_boxp_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {R3: SS.Relation (Kworlds M)} {R2_bis: Bisimulation SS.Krelation KM.Krelation} {SM: Semantics L MD} {fmSM: FlatModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x -> semantic_stable (boxp x).
Proof.
  intros.
  rewrite denote_stable in H |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_boxp _)).
  unfold Semantics.boxp; simpl.
  split.
  + pose proof bis_r _ _ H0.
    intros.
    specialize (H1 _ H3).
    destruct H1 as [m0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
  + pose proof bis_l _ _ H0.
    intros.
    rename n0 into m0.
    specialize (H1 _ H3).
    destruct H1 as [n0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
Qed.

Lemma sound_boxp_absorb_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {R3: SS.Relation (Kworlds M)} {R2_incl: Inclusion KM.Krelation SS.Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {fmSM: FlatModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x ->
    (forall (m: Kworlds M), KRIPKE: M, m |= x --> boxp x).
Proof.
  intros.
  rewrite sat_impp.
  intros.
  rewrite sat_boxp.
  intros.
  rewrite denote_stable in H.
  unfold Semantics.stable in H.
  apply including in H2.
  specialize (H _ _ H2).
  tauto.
Qed.

Lemma sound_sepcon_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {J: Join (Kworlds M)} {SAbis: SeparationAlgebraBisStable (Kworlds M)} {SM: Semantics L MD} {fsSM: SeparatingSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x * y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_sepcon _ _)).
  unfold WeakSemantics.sepcon; simpl.
  pose proof split_bis_stable _ _ H1.
  split; intros.
  + destruct H2 as [? _].
    destruct H3 as [m1 [m2 [? [? ?]]]].
    specialize (H2 _ _ H3).
    destruct H2 as [n1 [n2 [? [? ?]]]].
    exists n1, n2.
    specialize (H _ _ H6).
    specialize (H0 _ _ H7).
    tauto.
  + destruct H2 as [_ ?].
    destruct H3 as [n1 [n2 [? [? ?]]]].
    specialize (H2 _ _ H3).
    destruct H2 as [m1 [m2 [? [? ?]]]].
    exists m1, m2.
    specialize (H _ _ H6).
    specialize (H0 _ _ H7).
    tauto.
Qed.

Lemma sound_wand_stable {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {J: Join (Kworlds M)} {SAbis: SeparationAlgebraBisStable (Kworlds M)} {SM: Semantics L MD} {fsSM: SeparatingSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x -* y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_wand _ _)).
  unfold WeakSemantics.wand; simpl.
  pose proof extend_bis_stable _ _ H1.
  split.
  + intros ? n1 n2 ? ?.
    destruct H2 as [_ ?].
    specialize (H2 _ _ H4).
    destruct H2 as [m1 [m2 [? [? ?]]]].
    specialize (H3 _ _ H2).
    specialize (H0 _ _ H7).
    specialize (H _ _ H6).
    tauto.
  + intros ? m1 m2 ? ?.
    destruct H2 as [? _].
    specialize (H2 _ _ H4).
    destruct H2 as [n1 [n2 [? [? ?]]]].
    specialize (H3 _ _ H2).
    specialize (H0 _ _ H7).
    specialize (H _ _ H6).
    tauto.
Qed.

Lemma sound_stable_andp_sepcon1 {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {J: Join (Kworlds M)} {SAabs: SeparationAlgebraAbsorbStable (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {kminSM: KripkeMinimunSemantics L MD M SM} {kpSM: KripkePropositionalSemantics L MD M SM} {fsSM: SeparatingSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y z, semantic_stable x ->
    forall m: Kworlds M, KRIPKE: M, m |= (x && y) * z <--> x && (y * z).
Proof.
  intros.
  unfold iffp.
  rewrite sat_andp, !sat_impp.
  split; intros.
  + clear m H0.
    rewrite sat_andp, sat_sepcon.
    rewrite sat_sepcon in H1.
    destruct H1 as [n1 [n2 [? [? ?]]]].
    rewrite sat_andp in H1.
    destruct H1.
    destruct (SA_absorb_stable _ _ _ H0) as [m1 [m2 [? [? [? [? ?]]]]]].
    apply (sat_mono _ _ _ H7) in H1.
    apply (sat_mono _ _ _ H7) in H3.
    apply (sat_mono _ _ _ H8) in H2.
    rewrite denote_stable in H.
    rewrite (H _ _ H5) in H1.
    split; auto.
    exists m1, m2; auto.
  + clear m H0.
    rewrite sat_sepcon.
    rewrite sat_andp, sat_sepcon in H1.
    destruct H1 as [? [n1 [n2 [? [? ?]]]]].
    destruct (SA_absorb_stable _ _ _ H1) as [m1 [m2 [? [? [? [? ?]]]]]].
    apply (sat_mono _ _ _ H7) in H2.
    apply (sat_mono _ _ _ H8) in H3.
    rewrite denote_stable in H.
    rewrite <- (H _ _ H5) in H0.
    exists m1, m2.
    split; [| split]; auto.
    rewrite sat_andp.
    auto.
Qed.

End Sound_KripkeIntuitionistic.
