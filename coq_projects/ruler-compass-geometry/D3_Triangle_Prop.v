Require Export D2_Axe.

Section TRIANGLE_PROPERTIES.

Lemma TriangleSpecComm : forall A B C : Point,
	A <> B ->
	B <> C ->
	C <> A ->
	TriangleSpec (Distance A B) (Distance B C) (Distance C A) ->
	TriangleSpec (Distance A B) (Distance C A) (Distance B C) .
Proof.
	substDistance.
	rewrite (LSplusComm C A B C); auto.
	rewrite (LSplusComm B C A B); auto.
	rewrite (LSplusComm A B C A); auto.
	intuition.
Qed.

Lemma EqualTriangleClockwise : forall A B C D E : Point,
	Clockwise A B C ->
	Distance A B = Distance D E ->
	{F : Point |
		Clockwise D E F /\ 
		Distance B C = Distance E F /\
		Distance C A = Distance F D}.
Proof.
	intros.
	assert (H1 := ClockwiseDistinctBC A B C H).
	assert (H2 := ClockwiseDistinctCA A B C H).
	setCircle E B C H1 ipattern:(F1) ipattern:(G1).
	setCircle D C A H2 ipattern:(F2) ipattern:(G2).
	setCinterantiC F1 F2 G1 G2 ipattern:(F) ipattern:(H3) ipattern:(H4) ipattern:(H5)
	 ipattern:(H6).
	 rewrite (DistSym E D); rewrite <- H0.
	   apply ClockwiseTriangleSpec; auto.
	 exists F; canonize.
	   rewrite (DistSym F D); auto.
Qed.

Lemma EqualTriangleAntiClockwise : forall A B C D E : Point,
	Clockwise A B C ->
	Distance A B = Distance D E ->
	{F : Point |
		Clockwise D F E /\ 
		Distance B C = Distance E F /\
		Distance C A = Distance F D}.
Proof.
	intros.
	assert (H1 := ClockwiseDistinctBC A B C H).
	assert (H2 := ClockwiseDistinctCA A B C H).
	setCircle E B C H1 ipattern:(F1) ipattern:(G1).
	setCircle D C A H2 ipattern:(F2) ipattern:(G2).
	setCinterclockC F1 F2 G1 G2 ipattern:(F) ipattern:(H3) ipattern:(H4) ipattern:(H5)
	 ipattern:(H6).
	 rewrite (DistSym E D); rewrite <- H0.
	   apply ClockwiseTriangleSpec; auto.
	 exists F; canonize.
	  autoClockwise.
	  rewrite (DistSym F D); auto.
Qed.

Lemma ExistsCongruentStrictTriangle : forall A B C D E : Point,
	Clockwise A B C ->
	Distance A B = Distance D E ->
	{F : Point | CongruentStrictTriangles A B C D E F /\ Clockwise D E F}.
Proof.
	intros.
	destruct (EqualTriangleClockwise A B C D E H H0) as (F, (H1, (H2, H3))).
	exists F; repeat split; auto.
	apply ClockwiseNotCollinear; trivial.
Qed.

End TRIANGLE_PROPERTIES.
