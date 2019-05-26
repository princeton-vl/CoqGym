Require Export C10_Milieu.

Section MIDLINE.

Definition MidLineDef (A B : Point) : Figure := 
	fun M : Point => Distance M A = Distance M B.

Lemma CollinearMidLine : forall A B C D M : Point,	
	A <> B ->
	Distance C A = Distance C B ->
	Clockwise A B C ->
	Distance D A = Distance D B ->
	Clockwise B A D ->
	Collinear C D M ->
	Distance M A = Distance M B.
Proof.
	intros.
	assert (H5 := ClockwiseClockwiseDistinct A B C D H1 H3).
	destruct (CollinearHalfLine C D M H4).
	 assert (H7 := HalfLineDistinct C D M H5 H6).
	   apply (CongruentSAS C M A C M B); try autoDistinct; try autoDistance.
	   rewrite (CongruentItself C M A D A); try autoDistinct.
	  rewrite (CongruentItself C M B D B); try autoDistinct.
	   apply CongruentSSS; try autoDistinct; try autoDistance.
	   apply HalfLineSym; auto.
	  apply HalfLineSym; auto.
	 assert (H7 := HalfLineDistinct D C M (sym_not_eq H5) H6).
	   apply (CongruentSAS D M A D M B); try autoDistinct; try autoDistance.
	   rewrite (CongruentItself D M A C A); try autoDistinct.
	  rewrite (CongruentItself D M B C B); try autoDistinct.
	   apply CongruentSSS; try autoDistinct; try autoDistance.
	   apply HalfLineSym; auto.
	  apply HalfLineSym; auto.
Qed.

Lemma MidLineNotClockwise : forall A B C D M : Point,	
	A <> B ->
	Distance C A = Distance C B ->
	Clockwise A B C ->
	Distance D A = Distance D B ->
	Clockwise B A D ->
	Clockwise C D B ->
	Distance M A = Distance M B ->
	~Clockwise D C M.
Proof.
	red in |- *; intros.
	destruct (FourPointsIntersectionPoint C D B M H4 H6) as (N, (H7, H8)).
	assert (H9 := CollinearMidLine A B C D N H H0 H1 H2 H3 H7).
	assert (H10 : A <> N).
	 intro; subst; elim H.
	   apply DistNull; autoDistance.
	 assert (H11 : A <> M).
	  intro; subst; elim H.
	    apply DistNull; autoDistance.
	  assert (H12 := BetweenDistinctAB _ _ _ H8).
	    assert (H13 := BetweenDistinctCA _ _ _ H8).
	    assert (H14 := BetweenDistinctBC _ _ _ H8).
	    assert (H15 : Angle N B M = AS0).
	   apply (NullAngle B N M H12 (BetweenHalfLine _ _ _ H8)).
	   assert (H16 : Angle N A M = AS0).
	    rewrite <- H15.
	      apply CongruentSSS; try autoDistinct; try autoDistance.
	    destruct (MarkChange N M A B H14 H).
	     apply CollinearBCA; apply HalfLineCollinear; apply NullAngleHalfLine;
	      try autoDistinct.
	     apply CollinearBCA; apply HalfLineCollinear; apply NullAngleHalfLine;
	      try autoDistinct.
	     elim (BetweenDistinctBC _ _ _ H8);
	      apply trans_eq with (y := MidPoint A B H).
	      apply UniqueMidPoint; try autoDistance.
	        apply H17; unfold In in |- *; apply CollinearABA.
	      apply sym_eq; apply UniqueMidPoint; try autoDistance.
	        apply H17; unfold In in |- *; apply CollinearABB.
Qed.

Lemma ClockwiseDCA : forall A B C D : Point,	
	A <> B ->
	Distance C A = Distance C B ->
	Clockwise A B C ->
	Distance D A = Distance D B ->
	Clockwise B A D ->
	Clockwise D C A.
Proof.
	intros.
	assert (H4 := MidPointBetween A B H).
	assert (H5 := MidPointBetweenCD A B C D H H0 H2 H1 H3).
	apply (ClockwiseBetweenMBC D C A (MidPoint A B H)).
	 apply BetweenSym; trivial.
	 apply ClockwiseBCA; apply (BetweenClockwiseAMC A B C (MidPoint A B H) H1 H4).
Qed.

Lemma ClockwiseCDB : forall A B C D : Point,	
	A <> B ->
	Distance C A = Distance C B ->
	Clockwise A B C ->
	Distance D A = Distance D B ->
	Clockwise B A D ->
	Clockwise C D B.
Proof.
	intros.
	assert (H4 := MidPointBetween A B H).
	assert (H5 := MidPointBetweenCD A B C D H H0 H2 H1 H3).
	apply (ClockwiseBetweenAMC C D B (MidPoint A B H)).
	 trivial.
	 apply ClockwiseCAB; apply (BetweenClockwiseMBC A B C (MidPoint A B H) H1 H4).
Qed.

Lemma MidLine : forall A B : Point,
	A <> B ->
	Line (MidLineDef A B).
Proof.
	intros A B H.
	destruct (EquilateralClockwise A B H) as (C, ((H1, H2), H3)).
	destruct (EquilateralClockwise B A (sym_not_eq H)) as (D, ((H4, H5), H6)).
	assert (H7 := ClockwiseClockwiseDistinct A B C D H3 H6).
	apply (SuperimposedLine (Collinear C D)).
	 split; unfold SubFigure, MidLineDef, Included, In in |- *.
	  intros E H8.
	    pattern E in |- *; fold (MidLineDef A B) in |- *.
	    apply (CollinearMidLine A B C D E); unfold MidLineDef in |- *; auto.
	   rewrite (DistSym C A); rewrite (DistSym C B); autoDistance.
	   rewrite (DistSym D A); rewrite (DistSym D B); autoDistance.
	  intros E H8.
	    decompose [or] (ThreeCases C D E).
	   elim (MidLineNotClockwise B A D C E); try autoDistinct.
	    rewrite (DistSym D B); rewrite (DistSym D A); autoDistance.
	    rewrite (DistSym C B); rewrite (DistSym C A); autoDistance.
	    apply (ClockwiseDCA A B C D); auto.
	     rewrite (DistSym C A); rewrite (DistSym C B); autoDistance.
	     rewrite (DistSym D A); rewrite (DistSym D B); autoDistance.
	   elim (MidLineNotClockwise A B C D E); try autoDistinct.
	    rewrite (DistSym C A); rewrite (DistSym C B); autoDistance.
	    rewrite (DistSym D A); rewrite (DistSym D B); autoDistance.
	    apply (ClockwiseCDB A B C D); auto.
	     rewrite (DistSym C A); rewrite (DistSym C B); autoDistance.
	     rewrite (DistSym D A); rewrite (DistSym D B); autoDistance.
	   trivial.
	 apply Ruler.
	   trivial.
Qed.

End MIDLINE.
