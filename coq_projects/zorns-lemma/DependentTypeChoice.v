Require Import ClassicalChoice.

Set Asymmetric Patterns.

Lemma choice_on_dependent_type: forall {A:Type} {B:A->Type}
  (R:forall a:A, B a -> Prop),
  (forall a:A, exists b:B a, R a b) ->
  exists f:(forall a:A, B a), forall a:A, R a (f a).
Proof.
intros.
destruct (choice (fun (a:A) (b:{a:A & B a}) =>
  match b with existT a' b0 => a=a' /\ R a' b0 end))
as [choice_fun].
intro a.
destruct (H a) as [b].
exists (existT (fun a:A => B a) a b).
split; trivial.
assert (f0:forall a:A, {b:B a | R a b}).
intro.
pose proof (H0 a).
destruct (choice_fun a) as [a' b].
destruct H1.
destruct H1.
exists b; trivial.
exists (fun a:A => proj1_sig (f0 a)).
intro.
destruct (f0 a) as [b].
exact r.
Qed.
