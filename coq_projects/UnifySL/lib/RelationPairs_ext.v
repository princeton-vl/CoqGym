Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationPairs.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Equivalence.
Require Import Logic.lib.Relation_ext.
Require Import Logic.lib.Bisimulation.

Instance eq_preorder (A: Type): PreOrder (@eq A) :=
  Build_PreOrder _ (eq_Reflexive) (eq_Transitive).

Instance RelProd_Preorder:
  forall {A B : Type} (RA: relation A) (RB : relation B),
  PreOrder RA -> PreOrder RB -> PreOrder (RelProd RA RB).
Proof.
  intros.
  destruct H, H0.
  constructor.
  + apply RelProd_Reflexive; auto.
  + apply RelProd_Transitive; auto.
Qed.

Instance RelProd_PartialFunctional:
  forall {A B : Type} (RA: relation A) (RB : relation B),
  PartialFunctional RA -> PartialFunctional RB -> PartialFunctional (RelProd RA RB).
Proof.
  intros; hnf; intros.
  destruct m as [m1 m2], n as [n1 n2], n' as [n1' n2'], H1, H2.
  hnf in H1, H2, H3, H4; simpl in *.
  f_equal.
  + eapply H; eauto.
  + eapply H0; eauto.
Qed.

Instance RelProd_Bisimulation:
  forall {A B : Type} (bisA RA: relation A) (bisB RB : relation B),
  Bisimulation bisA RA -> Bisimulation bisB RB -> Bisimulation (RelProd bisA bisB) (RelProd RA RB).
Proof.
  intros.
  constructor; intros [m1 m2] [n1 n2] [? ?].
  + intros [m1' m2'] [? ?].
    hnf in H1, H2, H3, H4; simpl in *.
    destruct (@bis_l _ _ _ H _ _ H1 _ H3) as [n1' [? ?]].
    destruct (@bis_l _ _ _ H0 _ _ H2 _ H4) as [n2' [? ?]].
    exists (n1', n2'); auto.
  + intros [n1' n2'] [? ?].
    hnf in H1, H2, H3, H4; simpl in *.
    destruct (@bis_r _ _ _ H _ _ H1 _ H3) as [m1' [? ?]].
    destruct (@bis_r _ _ _ H0 _ _ H2 _ H4) as [m2' [? ?]].
    exists (m1', m2'); auto.
Qed.

Instance RelProd_Inclusion:
  forall {A B : Type} (RA1 RA2: relation A) (RB1 RB2 : relation B),
  Inclusion RA1 RA2 -> Inclusion RB1 RB2 -> Inclusion (RelProd RA1 RB1) (RelProd RA2 RB2).
Proof.
  intros.
  hnf; intros.
  destruct H1; split.
  + eapply H; eauto.
  + eapply H0; eauto.
Qed.

Instance pointwise_preorder:
  forall A {B : Type} (RB : relation B),
  PreOrder RB -> PreOrder (pointwise_relation A RB).
Proof.
  intros.
  destruct H.
  constructor.
  + apply pointwise_reflexive; auto.
  + apply pointwise_transitive; auto.
Qed.  

Inductive option00_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option00: option00_relation R None None
| Some_Some_option00: forall a b, R a b -> option00_relation R (Some a) (Some b).

Inductive option01_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option01: option01_relation R None None
| None_Some_option01: forall a, option01_relation R None (Some a)
| Some_Some_option01: forall a b, R a b -> option01_relation R (Some a) (Some b).

Instance option00_reflexive {A: Type} (R: relation A) {_: Reflexive R}: Reflexive (option00_relation R).
Proof.
  hnf; intros.
  destruct x.
  + constructor; reflexivity.
  + constructor.
Qed.

Instance option01_reflexive {A: Type} (R: relation A) {_: Reflexive R}: Reflexive (option01_relation R).
Proof.
  hnf; intros.
  destruct x.
  + constructor; reflexivity.
  + constructor.
Qed.

Instance option00_transitive {A: Type} (R: relation A) {_: Transitive R}: Transitive (option00_relation R).
Proof.
  hnf; intros.
  hnf; intros.
  inversion H0; inversion H1; subst; try first [congruence | constructor].
  inversion H6; subst.
  etransitivity; eauto.
Qed.

Instance option01_transitive {A: Type} (R: relation A) {_: Transitive R}: Transitive (option01_relation R).
Proof.
  hnf; intros.
  hnf; intros.
  inversion H0; inversion H1; subst; try first [congruence | constructor].
  inversion H6; subst.
  etransitivity; eauto.
Qed.

Instance option00_preorder {A: Type} (R: relation A) {_: PreOrder R}: PreOrder (option00_relation R)
  := Build_PreOrder _ (option00_reflexive R) (option00_transitive R).

Instance option01_preorder {A: Type} (R: relation A) {_: PreOrder R}: PreOrder (option01_relation R)
  := Build_PreOrder _ (option01_reflexive R) (option01_transitive R).

Inductive sum00_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum00_ll a1 a2: RA a1 a2 -> sum00_relation RA RB (inl a1) (inl a2)
  | sum00_rr b1 b2: RB b1 b2 -> sum00_relation RA RB (inr b1) (inr b2).

Inductive sum01_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum01_ll a1 a2: RA a1 a2 -> sum01_relation RA RB (inl a1) (inl a2)
  | sum01_lr a b: sum01_relation RA RB (inl a) (inr b)
  | sum01_rr b1 b2: RB b1 b2 -> sum01_relation RA RB (inr b1) (inr b2).

Instance sum00_reflexive {A B: Type} (RA: relation A) (RB: relation B) {_: Reflexive RA} {_: Reflexive RB}: Reflexive (sum00_relation RA RB).
Proof.
  hnf; intros.
  destruct x; constructor; auto.
Qed.

Instance sum01_reflexive {A B: Type} (RA: relation A) (RB: relation B) {_: Reflexive RA} {_: Reflexive RB}: Reflexive (sum01_relation RA RB).
Proof.
  hnf; intros.
  destruct x; constructor; auto.
Qed.

Instance sum00_transitive {A B: Type} (RA: relation A) (RB: relation B) {_: Transitive RA} {_: Transitive RB}: Transitive (sum00_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; inversion H2; subst;
  constructor;
  etransitivity; eauto.
Qed.

Instance sum01_transitive {A B: Type} (RA: relation A) (RB: relation B) {_: Transitive RA} {_: Transitive RB}: Transitive (sum01_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; inversion H2; subst;
  constructor;
  etransitivity; eauto.
Qed.

Instance sum00_preorder {A B: Type} (RA: relation A) (RB: relation B) {_: PreOrder RA} {_: PreOrder RB}: PreOrder (sum00_relation RA RB) :=
  Build_PreOrder _ (sum00_reflexive RA RB) (sum00_transitive RA RB).

Instance sum01_preorder {A B: Type} (RA: relation A) (RB: relation B) {_: PreOrder RA} {_: PreOrder RB}: PreOrder (sum01_relation RA RB) :=
  Build_PreOrder _ (sum01_reflexive RA RB) (sum01_transitive RA RB).

Definition true_relation (A: Type): relation A := fun _ _ => True.

Instance true_reflexive (A: Type): Reflexive (true_relation A).
Proof.
  hnf; intros.
  hnf; auto.
Qed.

Instance true_transitive (A: Type): Transitive (true_relation A).
Proof.
  hnf; intros.
  hnf; auto.
Qed.

Instance true_preorder (A: Type): PreOrder (true_relation A) :=
  Build_PreOrder _ (true_reflexive A) (true_transitive A).

