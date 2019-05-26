Require Import Arith.

Fixpoint le_bool (n m: nat) {struct n}: bool :=
  match n, m with
  O, _ => true
| S n1, S m1 => le_bool n1 m1
| _, _ => false
end.

Theorem le_correct: forall n m, le_bool n m = true -> n <= m.
induction n; destruct m; simpl; auto with arith; intros; discriminate.
Qed.

Fixpoint lt_bool (n m: nat) {struct n}: bool :=
  match n, m with
  O, (S _)  => true
| S n1, S m1 => lt_bool n1 m1
| _, _ => false
end.

Theorem lt_correct: forall n m, lt_bool n m = true -> n <= m.
induction n; destruct m; simpl; auto with arith; intros; discriminate.
Qed.

Hint Extern 4 (?X1 <= ?X2)%nat => exact (le_correct X1 X2 (refl_equal true)).
Hint Extern 4 (?X1 < ?X2)%nat => exact (lt_correct X1 X2 (refl_equal true)).
