Require Export B4_Droite_Def.

Section BETWEEN_PRELIMINARS.

Lemma BetweenDistinctAB : forall A B C, Between A B C -> A <> B.
Proof.
	canonize.
Qed.

Lemma BetweenNotClockwiseABC : forall A B C,
	Between A B C -> ~Clockwise A B C.
Proof.
	canonize.
	elim (NotClockwiseBAA C B).
	auto.
Qed.

Lemma ClockwiseNotBetweenABC : forall A B C,
	Clockwise A B C -> ~Between A B C.
Proof.
	canonize.
	elim (NotClockwiseBAA C B); auto.
Qed.

Lemma BetweenNotClockwiseBAC : forall A B C,
	Between A B C -> ~Clockwise B A C.
Proof.
	generalizeChange.
	elim (NotClockwiseBAA A B).
	apply H3; apply ClockwiseCAB; trivial.
Qed.

Lemma BetweenHalfLine : forall A B C,
	Between A B C -> HalfLine A B C.
Proof.
	intros; decompose [or] (FourCases A B C).
	 elim (BetweenNotClockwiseABC A B C H); trivial.
	 elim (BetweenNotClockwiseBAC A B C H); trivial.
	 trivial.
	 generalizeChange; elim (ClockwiseNotClockwise A B x); auto.
Qed.

Lemma BetweenSymHalfLine : forall A B C,
	Between A B C -> HalfLine C B A.
Proof.
	intros; decompose [or] (FourCases C B A).
	 elim (BetweenNotClockwiseBAC A B C H); apply ClockwiseBCA; trivial.
	 elim (BetweenNotClockwiseABC A B C H); apply ClockwiseCAB; trivial.
	 trivial.
	 generalizeChange; elim (ClockwiseNotClockwise B A x); auto.
Qed.

End BETWEEN_PRELIMINARS.
