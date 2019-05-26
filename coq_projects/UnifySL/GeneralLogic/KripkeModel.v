Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Export Logic.lib.Relation_ext.
Require Export Logic.lib.RelationPairs_ext.

Module KI.

Class Relation (worlds: Type): Type :=
  Krelation: worlds -> Ensemble worlds (* <= *).

End KI.

Export KI.

Module KripkeModelNotation_Intuitionistic.

Infix "<=" := Krelation: kripke_model.

End KripkeModelNotation_Intuitionistic.

Import KripkeModelNotation_Intuitionistic.

Local Open Scope kripke_model.

Definition upwards_closed_Kdenote {worlds: Type} {R: Relation worlds} (d: Ensemble worlds): Prop :=
  forall n m, n <= m -> d n -> d m.

Definition Krelation_stable_Kdenote {worlds: Type} {R: Relation worlds} (d: Ensemble worlds): Prop :=
  forall w1 w2, w1 <= w2 -> (d w1 <-> d w2).

Definition MonoEnsemble (A: Type) {R: Relation A}: Type := @sig (_ -> Prop) (@upwards_closed_Kdenote A R).

Class IdentityKripkeIntuitionisticModel (worlds: Type) {R: Relation worlds} : Prop := {
  Korder_identity: forall m n: worlds, m <= n -> m = n
}.

Class NoBranchKripkeIntuitionisticModel (worlds: Type) {R: Relation worlds} : Prop := {
  Korder_no_branch: forall m1 m2 n: worlds, n <= m1 -> n <= m2 -> m1 <= m2 \/ m2 <= m1
}.

Class BranchJoinKripkeIntuitionisticModel (worlds: Type) {R: Relation worlds} : Prop := {
  Korder_branch_join: forall m1 m2 n: worlds, n <= m1 -> n <= m2 -> exists m, m1 <= m /\ m2 <= m
}.

Instance prod_BranchJoinKripkeIntuitionisticModel (A B: Type) {RA: Relation A} {RB: Relation B} {bkiMA: BranchJoinKripkeIntuitionisticModel A} {bkiMB: BranchJoinKripkeIntuitionisticModel B}: @BranchJoinKripkeIntuitionisticModel (A * B) (RelProd RA RB).
Proof.
  constructor.
  intros [m11 m12] [m21 m22] [n1 n2] [? ?] [? ?].
  hnf in H, H0, H1, H2; simpl in *.
  destruct (@Korder_branch_join _ _ bkiMA m11 m21 n1 H H1) as [m1 [? ?]].
  destruct (@Korder_branch_join _ _ bkiMB m12 m22 n2 H0 H2) as [m2 [? ?]].
  exists (m1, m2); split; split; auto.
Qed.

Instance fun_BranchJoinKripkeIntuitionisticModel (A B: Type) {RB: Relation B} {bkiMB: BranchJoinKripkeIntuitionisticModel B}: @BranchJoinKripkeIntuitionisticModel (A -> B) (pointwise_relation A RB).
Proof.
  constructor.
  intros.
  destruct (choice (fun x fx => m1 x <= fx /\ m2 x <= fx)) as [m ?].
  + intros.
    specialize (H x).
    specialize (H0 x).
    destruct (Korder_branch_join _ _ _ H H0) as [y [? ?]].
    exists y; auto.
  + exists m.
    split; intros x; specialize (H1 x); tauto.
Qed.

Instance option00_BranchJoinKripkeIntuitionisticModel (A: Type) {R: Relation A} {bkiM: BranchJoinKripkeIntuitionisticModel A}: @BranchJoinKripkeIntuitionisticModel (option A) (option00_relation R).
Proof.
  constructor.
  intros.
  inversion H; inversion H0; try congruence; subst.
  + exists None; split; auto.
  + inversion H5; subst.
    clear H0 H H5.
    destruct (Korder_branch_join _ _ _ H1 H4) as [b' [? ?]].
    exists (Some b').
    split; constructor; auto.
Qed.

Instance NoBranch2BranchJoin (A: Type) {R: Relation A} {po_R: PreOrder Krelation} {nkiM: NoBranchKripkeIntuitionisticModel A}: BranchJoinKripkeIntuitionisticModel A.
Proof.
  constructor.
  intros.
  pose proof Korder_no_branch _ _ _ H H0.
  destruct H1.
  + exists m2; split; auto.
    reflexivity.
  + exists m1; split; auto.
    reflexivity.
Qed.

Instance eq_ikiM {worlds: Type}: @IdentityKripkeIntuitionisticModel worlds eq.
Proof.
  constructor.
  intros; auto.
Qed.

