Require Import Arith.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Lemma leb_false_lt : forall m n, leb m n = false -> n < m.
Proof.
  induction m; intros.
  - discriminate.
  - simpl in *.
    destruct n; subst; auto with arith.
Qed.
