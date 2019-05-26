Require Import IntuitionisticLogic.base.
Require Import IntuitionisticLogic.Wf.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Setoids.Setoid.
Local Open Scope IPC_scope.

Module RelationDef.
Section RelationDef.

Context {A: Type}.

Section Intersection.

Variables R1 R2: relation A.

Definition intersection x y := R1 x y /\ R2 x y.

End Intersection.

Arguments union {A} R1 R2 x y /.
Arguments intersection R1 R2 x y /.

Variables R eqA: relation A.

Class Total: Prop :=
  totality: forall x y, R x y \/ R y x.

Class StrictTotal: Prop :=
  strict_totality: forall x y, R x y \/ x = y \/ R y x.

Class StrictTotalViaEquiv: Prop :=
  strict_totality_via_equiv: forall x y, R x y \/ eqA x y \/ R y x.

Class Antisymmetric: Prop :=
  antisymmetry: forall x y, R x y -> R y x -> x = y.

Class AntisymViaEquiv: Prop :=
  antisymmetry_via_equiv: forall x y, R x y -> R y x -> eqA x y.

Class IrreflViaEquiv: Prop :=
  irreflexivity_via_equiv: forall x y, eqA x y -> R x y -> False.

Class WeakTotalOrder: Prop := {
  WeakTotalOrder_Reflexive: Reflexive R;
  WeakTotalOrder_Transitive: Transitive R;
  WeakTotalOrder_Total: Total
}.

Class TotalOrder: Prop := {
  TotalOrder_Reflexive: Reflexive R;
  TotalOrder_Antisymmetric: Antisymmetric;
  TotalOrder_Transitive: Transitive R;
  TotalOrder_Total: Total
}.

Class StrictTotalOrder: Prop := {
  StrictTotalOrder_Irreflexive: Irreflexive R;
  StrictTotalOrder_Transitive: Transitive R;
  StrictTotalOrder_StrictTotal: StrictTotal
}.

Class StrictTotalOrderViaEquiv: Prop := {
  StrictTotalOrderViaEquiv_EqIsEquiv: Equivalence eqA;
  StrictTotalOrderViaEquiv_IrreflViaEquiv: IrreflViaEquiv;
  StrictTotalOrderViaEquiv_Transitive: Transitive R;
  StrictTotalOrderViaEquiv_StrictTotal: StrictTotalViaEquiv
}.

Class StrictWellOrder: Prop := {
  StrictWellOrder_StrictTotalOrder: StrictTotalOrder;
  StrictWellOrder_WellFounded: well_founded R
}.

End RelationDef.

Lemma Irreflexive_is_IrreflViaEquiv:
  forall {A} (R: relation A),
  Irreflexive R <-> IrreflViaEquiv R eq.
Proof.
  intros; split; intros; hnf in *; intros.
  + subst.
    apply H in H1; auto.
  + specialize (H x x eq_refl).
    exact H.
Qed.

End RelationDef.

Import RelationDef.
Arguments union {A} R1 R2 x y /.
Arguments intersection {A} R1 R2 x y /.

Module StrictTotalOrderViaEquiv.
Section StrictTotalOrderViaEquiv.

Variable A: Type.
Variables R eqA: relation A.
Variable Order: StrictTotalOrderViaEquiv R eqA.

Lemma disjointed_3cases: forall x y,
  (R x y /\ ~ eqA x y /\ ~ R y x) \/
  (~ R x y /\ eqA x y /\ ~ R y x) \/
  (~ R x y /\ ~ eqA x y /\ R y x).
Proof.
  intros.
  pose proof StrictTotalOrderViaEquiv_StrictTotal _ _ x y.
  pose proof StrictTotalOrderViaEquiv_IrreflViaEquiv _ _ x y.
  pose proof StrictTotalOrderViaEquiv_IrreflViaEquiv _ _ y x.
  pose proof StrictTotalOrderViaEquiv_IrreflViaEquiv _ _ x x.
  pose proof StrictTotalOrderViaEquiv_Transitive _ _ x y x.
  inversion Order.
  pose proof Equivalence_Reflexive x.
  pose proof Equivalence_Symmetric x y.
  pose proof Equivalence_Symmetric y x.
  tauto.
Qed.
  
Lemma LeftProperViaEquiv: forall x x0 y, eqA x x0 -> R x y -> R x0 y.
Proof.
  intros.
  pose proof disjointed_3cases x0 y.
  pose proof disjointed_3cases x x0.
  pose proof disjointed_3cases x y.
  pose proof @Equivalence_Transitive _ eqA (StrictTotalOrderViaEquiv_EqIsEquiv _ _) x x0 y.
  pose proof StrictTotalOrderViaEquiv_Transitive _ _ x y x0.
  tauto.
Qed.  

Lemma RightProperViaEquiv: forall x y y0, eqA y0 y -> R x y -> R x y0.
Proof.
  intros.
  pose proof disjointed_3cases x y.
  pose proof disjointed_3cases y0 y.
  pose proof disjointed_3cases x y0.
  pose proof @Equivalence_Transitive _ eqA (StrictTotalOrderViaEquiv_EqIsEquiv _ _) x y0 y.
  pose proof StrictTotalOrderViaEquiv_Transitive _ _ y0 x y.
  tauto.
Qed.

Instance ProperViaEquiv: Proper (eqA ==> eqA ==> iff) R.
Proof.
  intro; intros; intro; intros.
  inversion Order.
  pose proof Equivalence_Symmetric _ _  H.
  pose proof Equivalence_Symmetric _ _  H0.
  pose proof LeftProperViaEquiv x y x0 H.
  pose proof LeftProperViaEquiv y x x0 H1.
  pose proof RightProperViaEquiv y x0 y0 H2.
  pose proof RightProperViaEquiv y y0 x0 H0.
  tauto.
Qed.

End StrictTotalOrderViaEquiv.

Theorem StrictTotalOrder_is_StrictTotalOrderViaEquiv:
  forall {A} (R: relation A), StrictTotalOrder R <-> StrictTotalOrderViaEquiv R eq.
Proof.
  intros; split; intros; inversion H; constructor; auto.
  + apply eq_equivalence.
  + apply Irreflexive_is_IrreflViaEquiv; auto.
  + apply Irreflexive_is_IrreflViaEquiv; auto.
Qed.
  
End StrictTotalOrderViaEquiv.

Section Operators.

Variable A: Type.
Variable R1 R2 eqA: relation A.

Lemma intersection_Reflexive: Reflexive R1 -> Reflexive R2 -> Reflexive (intersection R1 R2).
Proof.
  intros ? ? x.
  split; apply reflexivity.
Qed.

Lemma intersection_Symmetric: Symmetric R1 -> Symmetric R2 -> Symmetric (intersection R1 R2).
Proof.
  intros ? ? x y [? ?].
  split; apply symmetry; auto.
Qed.

Lemma intersection_Transitive: Transitive R1 -> Transitive R2 -> Transitive (intersection R1 R2).
Proof.
  intros ? ? x y z [? ?] [? ?].
  split; eapply transitivity; eauto.
Qed.

Lemma union_IrreflViaEquiv: IrreflViaEquiv R1 eqA -> IrreflViaEquiv R2 eqA -> IrreflViaEquiv (union R1 R2) eqA.
Proof.
  intros ? ? x y ? [? | ?].
  + exact (H x y H1 H2).
  + exact (H0 x y H1 H2).
Qed.

Theorem intersection_Equivalence: Equivalence R1 -> Equivalence R2 -> Equivalence (intersection R1 R2).
Proof.
  intros.
  constructor.
  + apply intersection_Reflexive; apply Equivalence_Reflexive.
  + apply intersection_Symmetric; apply Equivalence_Symmetric.
  + apply intersection_Transitive; apply Equivalence_Transitive.
Qed.

End Operators.

Section BiKeyOrder.

Variable A: Type.
Variable R1 R2 eqA1 eqA2: relation A.

Definition BiKey := union R1 (intersection eqA1 R2).

Theorem BiKey_StrictTotalOrderViaEquiv:
  StrictTotalOrderViaEquiv R1 eqA1 ->
  StrictTotalOrderViaEquiv R2 eqA2 ->
  StrictTotalOrderViaEquiv BiKey (intersection eqA1 eqA2).
Proof.
  intros; unfold BiKey.
  inversion H.
  inversion H0.
  constructor.
  + apply intersection_Equivalence; auto.
  + intros x y; simpl.
    specialize (StrictTotalOrderViaEquiv_IrreflViaEquiv0 x y).
    specialize (StrictTotalOrderViaEquiv_IrreflViaEquiv1 x y).
    tauto.
  + intros x y z [? | [? ?]] [? | [? ?]]; simpl.
    - left. eapply StrictTotalOrderViaEquiv_Transitive0; eauto.
    - left. eapply StrictTotalOrderViaEquiv.RightProperViaEquiv with (eqA := eqA1); eauto.
      symmetry; auto.
    - left. eapply StrictTotalOrderViaEquiv.LeftProperViaEquiv with (eqA := eqA1); eauto.
      symmetry; auto.
    - right; split.
      * eapply transitivity; eauto.
      * eapply transitivity; eauto.
  + intros x y; simpl.
    pose proof StrictTotalOrderViaEquiv.disjointed_3cases _ R1 _ _ x y.
    pose proof StrictTotalOrderViaEquiv.disjointed_3cases _ R2 _ _ x y.
    pose proof @symmetry _ eqA1 _ x y.
    pose proof @symmetry _ eqA1 _ y x.
    tauto.
Qed.

Lemma BiKey_StrictTotalOrder:
  StrictTotalOrderViaEquiv R1 eqA1 ->
  StrictTotalOrder R2 ->
  StrictTotalOrder BiKey.
Proof.
Admitted.

Section enumerate.

Variable venv: Var_env.
Variable lt_var: Var -> Var -> Prop.
Hypothesis Wf: well_founded lt_var.
Hypothesis TO: TotalOrder lt_var.

Fixpoint level (e: Term) : nat :=
  match e with
  | andp e1 e2 => max (level e1) (level e2) + 1
  | orp e1 e2 => max (level e1) (level e2) + 1
  | impp e1 e2 => max (level e1) (level e2) + 1
  | falsep => 0
  | varp _ => 0
  end.

Fixpoint trivial_lt (e1 e2: Term): Prop :=
  match e1, e2 with
  | falsep, falsep => False
  | falsep, _ => True
  | _, falsep => False
  | varp v1, varp v2 => lt_var v1 v2
  | varp _, _ => True
  | _, varp _ => False
  | andp e11 e12, andp e21 e22 => trivial_lt e11 e21 \/ (e11 = e21 /\ trivial_lt e12 e22)
  | andp _ _, _ => True
  | _, andp _ _ => False
  | orp e11 e12, orp e21 e22 => trivial_lt e11 e21 \/ (e11 = e21 /\ trivial_lt e12 e22)
  | orp _ _, _ => True
  | _, orp _ _ => False
  | impp e11 e12, impp e21 e22 => trivial_lt e11 e21 \/ (e11 = e21 /\ trivial_lt e12 e22)
  end.

Definition lt_Term (e1 e2: Term): Prop :=
  (level e1 < level e2) \/ (level e1 = level e2 /\ trivial_lt e1 e2).



Definition 
