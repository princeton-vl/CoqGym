Set Implicit Arguments.

Section Definitions.
Variables (A : Type).
Implicit Types f g : A -> A -> A.
Implicit Types i : A -> A.

Definition involutive i := forall x,
  i (i x) = x.
End Definitions.

Definition neg (x:bool) : bool :=
  match x with
  | true => false
  | false => true
  end.

Lemma neg_neg : involutive neg.
Proof.
intros x.
destruct x; auto.
Qed.

Hint Rewrite neg_neg : rew_neg_neg.
