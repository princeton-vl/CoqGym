Definition compare (x y : bool) : comparison :=
  match x, y with
  | true, false => Gt
  | false, true => Lt
  | true, true | false, false => Eq
  end.

Lemma compare_implies_eq : forall (x y : bool), compare x y = Eq -> x = y.
  intros x y; destruct x; destruct y; simpl; congruence.
Qed.

Lemma compare_same_is_eq : forall (x : bool), compare x x = Eq.
  intro x; destruct x; simpl; reflexivity.
Qed.