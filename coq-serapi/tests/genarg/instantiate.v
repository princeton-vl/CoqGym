Set Implicit Arguments.

Require Import List.

Section Filter.

Variable A : Type.

Lemma In_filter_In :
  forall (f : A -> bool) x l l',
    filter f l = l' ->
    In x l' -> In x l.
Proof.
  intros. subst.
  eapply filter_In.
  instantiate (1 := f).
  assumption.
Qed.

End Filter.
