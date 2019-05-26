Require Export A6_Intersection.

Section SUPERIMPOSED_EQUIVALENCE.

Lemma SuperimposedRefl : forall F : Figure,
	Superimposed F F.
Proof.
	dintuition; canonize.
Qed.

Lemma SuperimposedSym : forall F1 F2 : Figure,
	Superimposed F1 F2 -> Superimposed F2 F1.
Proof.
	dintuition; canonize.
Qed.

Lemma SuperimposedTrans : forall F1 F2 F3 : Figure,
	Superimposed F1 F2 -> Superimposed F2 F3 -> Superimposed F1 F3.
Proof.
	dintuition; canonize.
Qed.

Lemma SuperimposedHalfLines : forall A B C : Point,
	A <> B ->
	HalfLine A B C ->
	Superimposed (HalfLine A B) (HalfLine A C).
Proof.
	canonize; generalizeChange.
Qed.

End SUPERIMPOSED_EQUIVALENCE.
