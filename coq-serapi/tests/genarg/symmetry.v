Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section list_util.
  Variables A : Type.

  Lemma list_neq_cons :
    forall (l : list A) x,
      x :: l <> l.
  Proof using.
    intuition.
    symmetry in H.
    induction l;
      now inversion H.
  Qed.
End list_util.
