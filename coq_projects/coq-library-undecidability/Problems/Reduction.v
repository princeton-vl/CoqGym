Require Export Shared.Prelim.

Definition reduces X Y (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).
Notation "p ⪯ q" := (reduces p q) (at level 50).

Lemma reduces_reflexive X (p : X -> Prop) : p ⪯ p.
Proof. exists (fun x => x); tauto. Qed.

Lemma reduces_transitive X Y Z (p : X -> Prop) (q : Y -> Prop) (r : Z -> Prop) :
  p ⪯ q -> q ⪯ r -> p ⪯ r.
Proof.
  intros [f ?] [g ?]. exists (fun x => g (f x)). firstorder.
Qed.

