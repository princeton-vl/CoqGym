Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Model.OSAExamples.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Module SS.

Class Relation (worlds: Type): Type :=
  Krelation: worlds -> Ensemble worlds.

End SS.

Export SS.

Module Semantics.

Definition stable {worlds: Type} {R: Relation worlds} (X: Ensemble worlds): Prop := forall m n, R m n -> (X m <-> X n).

End Semantics.

Class SeparationAlgebraBisStable (worlds: Type) {J: Join worlds} {R: Relation worlds}: Type := {
  split_bis_stable:
    forall m n, R m n ->
      (forall m1 m2, join m1 m2 m -> exists n1 n2, join n1 n2 n /\ R m1 n1 /\ R m2 n2) /\
       (forall n1 n2, join n1 n2 n -> exists m1 m2, join m1 m2 m /\ R m1 n1 /\ R m2 n2);
  extend_bis_stable:
    forall m n, R m n ->
      (forall m1 m2, join m m1 m2 -> exists n1 n2, join n n1 n2 /\ R m1 n1 /\ R m2 n2) /\
       (forall n1 n2, join n n1 n2 -> exists m1 m2, join m m1 m2 /\ R m1 n1 /\ R m2 n2)
}.

Class SeparationAlgebraAbsorbStable (worlds: Type) {R1: KI.Relation worlds} {J: Join worlds} {R2: Relation worlds}: Type := {
  SA_absorb_stable:
    forall m m1 m2, join m1 m2 m ->
      exists n1 n2, join n1 n2 m /\ R2 n1 m /\ R2 n2 m /\ m1 <= n1 /\ m2 <= n2
}.

Class StrongSeparationAlgebraAbsorbStable (worlds: Type) {J: Join worlds} {R: Relation worlds}: Type := {
  strong_SA_absorb_stable:
    forall m m1 m2, join m1 m2 m -> R m1 m /\ R m2 m
}.

Lemma DownwardsClosure_SAAbsorbStable (worlds: Type) {R1: KI.Relation worlds} {po_R: PreOrder KI.Krelation} {J: Join worlds} {R2: Relation worlds} {SA_abs': StrongSeparationAlgebraAbsorbStable worlds}: @SeparationAlgebraAbsorbStable worlds R1 DownwardsClosure_J R2.
Proof.
  constructor.
  intros.
  hnf in H.
  destruct H as [n1 [n2 [? [? ?]]]].
  exists n1, n2.
  split; [| split; [| split; [| split ]]]; auto.
  + exists n1, n2.
    split; [| split]; auto; reflexivity.
  + destruct (strong_SA_absorb_stable _ _ _ H1); auto.
  + destruct (strong_SA_absorb_stable _ _ _ H1); auto.
Qed.

Instance prod_SAbis (A B: Type) (JA: Join A) (JB: Join B) (RA: SS.Relation A) (RB: SS.Relation B) {SAbisA: SeparationAlgebraBisStable A} {SAbisB: SeparationAlgebraBisStable B}: @SeparationAlgebraBisStable (A * B) (@prod_Join _ _ JA JB) (RelProd RA RB).
Proof.
  constructor.
  + intros [m1 m2] [n1 n2] [? ?].
    pose proof (@split_bis_stable A _ _ SAbisA m1 n1 H).
    pose proof (@split_bis_stable B _ _ SAbisB m2 n2 H0).
    split.
    - intros [n11 n12] [n21 n22] [? ?].
      destruct H1 as [? _].
      destruct H2 as [? _].
      specialize (H1 _ _ H3).
      destruct H1 as [m11 [m21 [? [? ?]]]].
      specialize (H2 _ _ H4).
      destruct H2 as [m12 [m22 [? [? ?]]]].
      exists (m11, m12), (m21, m22).
      split; [| split]; split; auto.
    - intros [m11 m12] [m21 m22] [? ?].
      destruct H1 as [_ ?].
      destruct H2 as [_ ?].
      specialize (H1 _ _ H3).
      destruct H1 as [n11 [n21 [? [? ?]]]].
      specialize (H2 _ _ H4).
      destruct H2 as [n12 [n22 [? [? ?]]]].
      exists (n11, n12), (n21, n22).
      split; [| split]; split; auto.
  + intros [m1 m2] [n1 n2] [? ?].
    pose proof (@extend_bis_stable A _ _ SAbisA m1 n1 H).
    pose proof (@extend_bis_stable B _ _ SAbisB m2 n2 H0).
    split.
    - intros [n11 n12] [n21 n22] [? ?].
      destruct H1 as [? _].
      destruct H2 as [? _].
      specialize (H1 _ _ H3).
      destruct H1 as [m11 [m21 [? [? ?]]]].
      specialize (H2 _ _ H4).
      destruct H2 as [m12 [m22 [? [? ?]]]].
      exists (m11, m12), (m21, m22).
      split; [| split]; split; auto.
    - intros [m11 m12] [m21 m22] [? ?].
      destruct H1 as [_ ?].
      destruct H2 as [_ ?].
      specialize (H1 _ _ H3).
      destruct H1 as [n11 [n21 [? [? ?]]]].
      specialize (H2 _ _ H4).
      destruct H2 as [n12 [n22 [? [? ?]]]].
      exists (n11, n12), (n21, n22).
      split; [| split]; split; auto.
Qed.    

Instance prod_SAabs (A B: Type) (R1A: KI.Relation A) (R1B: KI.Relation B) (JA: Join A) (JB: Join B) (R2A: SS.Relation A) (R2B: SS.Relation B) {SAabsA: SeparationAlgebraAbsorbStable A} {SAabsB: SeparationAlgebraAbsorbStable B}: @SeparationAlgebraAbsorbStable (A * B) (RelProd R1A R1B) (@prod_Join _ _ JA JB) (RelProd R2A R2B).
Proof.
  constructor.
  intros [m1 m2] [m11 m12] [m21 m22] [? ?].
  destruct (@SA_absorb_stable _ _ _ _ SAabsA _ _ _ H) as [n11 [n21 [? [? [? [? ?]]]]]].
  destruct (@SA_absorb_stable _ _ _ _ SAabsB _ _ _ H0) as [n12 [n22 [? [? [? [? ?]]]]]].
  exists (n11, n12), (n21, n22).
  split; [| split; [| split; [| split]]]; split; auto.
Qed.

Instance full_SAbis (A: Type) {R: KI.Relation A} {po_R: PreOrder KI.Krelation} {J: Join A} {SA: SeparationAlgebra A} {dSA: DownwardsClosedSeparationAlgebra A} {resSA: ResidualSeparationAlgebra A} : @SeparationAlgebraBisStable A J full_relation.
Proof.
  constructor.
  + intros; split; intros.
    - destruct (residue_exists n) as [n1 [n2 [? ?]]].
      exists n1, n2; auto.
    - destruct (residue_exists m) as [m1 [m2 [? ?]]].
      exists m1, m2; auto.
  + intros; split; intros.
    - destruct (residual_extensible n) as [n1 [n2 ?]].
      exists n1, n2; auto.
    - destruct (residual_extensible m) as [m1 [m2 ?]].
      exists m1, m2; auto.
Qed.

Instance full_SAabs (A: Type) {R: KI.Relation A} {po_R: PreOrder KI.Krelation} {J: Join A} : @SeparationAlgebraAbsorbStable A R J full_relation.
Proof.
  constructor.
  intros.
  exists m1, m2.
  split; [| split; [| split; [| split]]]; solve [hnf; auto | reflexivity].
Qed.

Instance eq_SAbis (A: Type) {J: Join A}: @SeparationAlgebraBisStable A J eq.
Proof.
  constructor.
  + intros; subst; split; intros.
    - exists m1, m2; auto.
    - exists n1, n2; auto.
  + intros; subst; split; intros.
    - exists m1, m2; auto.
    - exists n1, n2; auto.
Qed.

Instance geR_min_eq_SAabs: @SeparationAlgebraAbsorbStable nat nat_geR min_Join eq.
Proof.
  constructor.
  intros.
  exists m, m.
  inversion H; subst.
  split; [| split; [| split; [| split]]]; auto.
  constructor; auto.
Qed.

Require Import Logic.GeneralLogic.Base.

Class SemanticStable (L: Language) (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD): Type := {
  semantic_stable: expr -> Prop;
  denote_stable: forall x, semantic_stable x <-> Semantics.stable (Kdenotation M x)
}.

