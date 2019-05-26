Require Export Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.Equivalence.
Require Import Logic.lib.Relation_ext.

Definition bisimulation {A: Type} (bis: relation A) (R: relation A): Prop :=
  forall m n, bis m n ->
    (forall m', R m m' -> exists n', R n n' /\ bis m' n') /\
    (forall n', R n n' -> exists m', R m m' /\ bis m' n').

Class Bisimulation {A: Type} (bis: relation A) (R: relation A): Prop := {
  bis_l: forall m n, bis m n ->
            forall m', R m m' -> exists n', R n n' /\ bis m' n';
  bis_r: forall m n, bis m n ->
            forall n', R n n' -> exists m', R m m' /\ bis m' n'
}.

Lemma eq_bis {A: Type} (R: relation A): Bisimulation eq R.
Proof.
  constructor; intros.
  + exists m'; subst; auto.
  + exists n'; subst; auto.
Qed.

Lemma full_bis {A: Type} (R: relation A) {_: Serial R}: Bisimulation full_relation R.
Proof.
  constructor; intros.
  + destruct (seriality n) as [n' ?]; exists n'.
    auto.
  + destruct (seriality m) as [m' ?]; exists m'.
    auto.
Qed.

