Require Export B12_Tacticques_base.

Section HALFLINE_PROPERTIES.

Lemma HalfLineNotClockwiseABC : forall A B C,
	HalfLine A B C -> ~Clockwise A B C.
Proof.
	canonize.
	elim (ClockwiseDistinctBC A C C); auto.
Qed.

Lemma HalfLineNotClockwiseBAC : forall A B C,
	HalfLine A B C -> ~Clockwise B A C.
Proof.
	canonize; generalizeChangeSense.
	elim (ClockwiseDistinctCA C A C); auto.
Qed.

Lemma HalfLineCollinear : forall A B C,
	HalfLine A B C -> Collinear A B C.
Proof.
	intros; split.
	 exact (HalfLineNotClockwiseABC A B C H).
	 exact (HalfLineNotClockwiseBAC A B C H).
Qed.

Lemma HalfLineSym : forall A B C,
	A <> B ->
	HalfLine A B C ->
	HalfLine A C B.
Proof.
	generalizeChange.
Qed.

Lemma ClockwiseNotHalfLine : forall A B C,
	Clockwise A B C ->
	~HalfLine A B C.
Proof.
	intros A B C H H0.
	elim (ClockwiseNotCollinear A B C H).
	apply HalfLineCollinear; trivial.
Qed.

Lemma HalfLineDistinct : forall A B C,
	A <> B ->
	HalfLine A B C ->
	A <> C.
Proof.
	canonize.
	destruct (ClockwiseExists A B H) as (D, H2).
	assert (Clockwise A C D); [ auto | autoDistinct ].
Qed.

End HALFLINE_PROPERTIES.

