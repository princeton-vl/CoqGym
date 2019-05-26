Require Export C8_DroitesConfondues.

Section EMBEDDED_TRIANGLES.

Lemma BetweenClockwiseAMC : forall A B C M : Point,
	Clockwise A B C ->
	Between A M B ->
	Clockwise A M C.
Proof.
	intros A B C M H H0.
	assert (H1 := BetweenHalfLine _ _ _ H0).
	generalizeChange.
Qed.

Lemma BetweenClockwiseMBC : forall A B C M : Point,
	Clockwise A B C ->
	Between A M B ->
	Clockwise M B C.
Proof.
	intros A B C M H H0.
	assert (H1 := BetweenHalfLine _ _ _ H0).
	generalizeChange.
Qed.

Lemma ClockwiseBetweenAMC : forall A B C M : Point,
	Between A M B ->
	Clockwise A M C ->
	Clockwise A B C.
Proof.
	intros A B C M H H0.
	assert (H1 := BetweenHalfLine _ _ _ H).
	generalizeChange.
Qed.

Lemma ClockwiseBetweenMBC : forall A B C M : Point,
	Between A M B ->
	Clockwise M B C ->
	Clockwise A B C.
Proof.
	intros A B C M H H0.
	assert (H1 := BetweenHalfLine _ _ _ (BetweenSym _ _ _ H)).
	generalizeChange.
Qed.

Lemma TriangleAMN : forall A B C M N : Point,
	Clockwise A B C ->
	Between A M B ->
	Between A N C ->
	Clockwise A M N.
Proof.
	intros A B C M N H H0 H1.
	apply (BetweenClockwiseAMC A B N M).
	 apply ClockwiseBCA; apply (BetweenClockwiseMBC C A B N).
	  autoClockwise.
	  apply BetweenSym; trivial.
	 trivial.
Qed.

Lemma TriangleBNM : forall A B C M N : Point,
	Clockwise A B C ->
	Between A M B ->
	Between A N C ->
	Clockwise B N M.
Proof.
	intros A B C M N H H0 H1.
	apply ClockwiseBCA.
	assert (H2 := TriangleAMN A B C M N H H0 H1).
	canonize.
Qed.

Lemma TriangleCNM : forall A B C M N : Point,
	Clockwise A B C ->
	Between A M B ->
	Between A N C ->
	Clockwise C N M.
Proof.
	intros A B C M N H H0 H1.
	assert (H2 := TriangleAMN A B C M N H H0 H1).
	apply (BetweenClockwiseAMC C A M N).
	 apply (ClockwiseBetweenMBC C A M N).
	  apply BetweenSym; trivial.
	  autoClockwise.
	 apply BetweenSym; trivial.
Qed.

Lemma BetweenTriangle : forall A B C D M : Point,
	Clockwise A C D ->
	Clockwise B C D ->
	Between A M B ->
	Clockwise M C D.
Proof.
	intros A B C D M H H0 H1.
	decompose [or] (FourCases C D M).
	 autoClockwise.
	 destruct (FourPointsIntersectionPoint C D A M) as (I, (H4, H5)).
	  autoClockwise.
	  autoClockwise.
	  destruct (FourPointsIntersectionPoint C D B M) as (J, (H6, H7)).
	   autoClockwise.
	   autoClockwise.
	   elim (ClockwiseNotCollinear _ _ _ H3).
	     assert (I <> J).
	    intro; subst.
	      destruct
	       (ClockwiseExists M A (sym_not_eq (BetweenDistinctAB _ _ _ H1)))
	       as (K, H8).
	      elim (ClockwiseNotClockwise _ _ _ H8).
	      apply (ClockwiseBetweenMBC A M K J H5).
	      apply (BetweenClockwiseMBC B M K J).
	     assert (H9 := BetweenSym _ _ _ H1).
	       apply (BetweenClockwiseAMC B A K M).
	      apply (ClockwiseBetweenMBC B A K M H9 H8).
	      trivial.
	     trivial.
	    assert (H8 := ClockwiseDistinctBC _ _ _ H).
	      destruct (MarkChange C D I J H8 H2 H4 H6) as (H9, H10).
	      destruct (MarkChange A B I J) as (H11, H12).
	     assert (H11 := BetweenDistinctCA _ _ _ H1); auto.
	     trivial.
	     apply (CollinearTrans A M B I).
	      autoDistinct.
	      apply BetweenCollinear; trivial.
	      apply CollinearACB; apply BetweenCollinear; trivial.
	     apply CollinearBAC; apply (CollinearTrans B M A J).
	      assert (H11 := BetweenDistinctBC _ _ _ H1); auto.
	      apply CollinearCBA; apply BetweenCollinear; trivial.
	      apply CollinearACB; apply BetweenCollinear; trivial.
	     apply CollinearBAC; apply H10.
	       apply H11; change (Collinear A B M) in |- *.
	       apply CollinearACB; apply BetweenCollinear; trivial.
	 elim (ClockwiseNotClockwise C D B).
	  autoClockwise.
	  assert (Clockwise M C B).
	   assert (Clockwise A C M).
	    canonize.
	      apply ClockwiseCAB; apply H2; autoClockwise.
	    apply ClockwiseBCA; apply (BetweenClockwiseAMC B A C M).
	     apply (ClockwiseBetweenMBC B A C M).
	      apply BetweenSym; trivial.
	      autoClockwise.
	     apply BetweenSym; trivial.
	   generalizeChangeSide.
	     apply H1.
	    autoDistinct.
	    trivial.
	 elim (ClockwiseNotClockwise C D B).
	  autoClockwise.
	  assert (Clockwise M D A).
	   generalizeChangeSense.
	     apply H1; autoClockwise.
	   assert (Clockwise D M B).
	    apply ClockwiseCAB; apply (BetweenClockwiseMBC A B D M).
	     apply (ClockwiseBetweenAMC A B D M H1); autoClockwise.
	     trivial.
	    generalizeChange.
	      apply H9.
	     autoDistinct.
	     trivial.
Qed.

Lemma TriangleMNP : forall A B C M N P : Point,
	Clockwise A B C ->
	Between A M B ->
	Between B N C ->
	Between C P A ->
	Clockwise M N P.
Proof.
	intros A B C M N P H H0 H1 H2.
	apply (BetweenTriangle A B N P M).
	 apply (TriangleBNM C A B P N).
	  autoClockwise.
	  trivial.
	  apply BetweenSym; trivial.
	 apply (TriangleCNM C A B P N).
	  autoClockwise.
	  trivial.
	  apply BetweenSym; trivial.
	 trivial.
Qed.

Lemma ClockwiseBetween : forall A B C D : Point,
	Clockwise A B D ->
	Clockwise B C D ->
	Collinear A B C ->
	Between A B C.
Proof.
	intros; apply HalfLineBetween.
	 autoDistinct.
	 autoDistinct.
	 destruct (CollinearHalfLine _ _ _ H1).
	  trivial.
	  elim (ClockwiseNotClockwise _ _ _ H); generalizeChange.
	    apply H6.
	   autoDistinct.
	   trivial.
	 destruct (CollinearHalfLine _ _ _ (CollinearCBA _ _ _ H1)).
	  trivial.
	  elim (ClockwiseNotClockwise _ _ _ H); canonize.
Qed.

End EMBEDDED_TRIANGLES.
