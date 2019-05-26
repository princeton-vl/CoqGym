Require Export D3_Triangle_Prop.

Section CONSEQUENCES.

Lemma AS0diffASpi : AS0  <> ASpi.
Proof.
	unfold AS0, ASpi in |- *; intro H.
	elim (BetweenDistinctCA _ _ _ BetweenWwOoUu).
	apply DistNull; rewrite <- (NullDist Uu).
	apply (CongruentSAS Oo Uu Ww Oo Uu Uu).
	 exact DistinctOoUu.
	 exact DistinctOoWw.
	 trivial.
	 rewrite <- DistOoWw; autoDistance.
	 auto.
Qed.

Lemma ElongatedAngleBetween : forall A B C : Point, 
		A <> B ->
		A <> C ->
		Angle B A C = ASpi ->
		Between B A C.
Proof.
	intros.
	assert (H2 := ElongatedAngleChasles A B C H H0 H1).
	decompose [and] (ChaslesRec B A C H2).
	apply HalfLineBetween; auto.
Qed.

Lemma ProperAngle : forall A B C : Point, 
	Clockwise B A C -> 
	Angle B A C <> AS0 /\ Angle B A C <> ASpi.
Proof.
	intuition.
	 elim (ClockwiseNotHalfLine A C B).
	  autoClockwise.
	  apply NullAngleHalfLine; [ autoDistinct | autoDistinct | idtac ].
	    rewrite AngleSym; [ auto | autoDistinct | autoDistinct ].
	 elim (ClockwiseNotBetweenABC B A C H).
	   apply ElongatedAngleBetween; [ autoDistinct | autoDistinct | auto ].
Qed.

Lemma EqualAngleHalfLineB : forall A B B' C : Point,
	A <> C ->
	A <> B ->
	A <> B' ->
	~Clockwise A B C ->
	~Clockwise A B' C ->
	(Angle  B A C) = (Angle  B' A C) ->
	HalfLine A B B'.
Proof.
	intros.
	decompose [or] (ExclusiveFourCases A B C H);
	 decompose [or] (ExclusiveFourCases A B' C H).
	 elim H2; trivial.
	 elim H2; trivial.
	 elim H2; trivial.
	 elim H2; trivial.
	 elim H3; trivial.
	 apply (AngleCHalfLine A C B B'); auto.
	  autoClockwise.
	  autoClockwise.
	  rewrite AngleSym; auto.
	    rewrite H4; apply AngleSym; auto.
	 destruct (ProperAngle A B C H6).
	   elim H7; rewrite H4; apply NullAngle; auto.
	 destruct (ProperAngle A B C H6).
	   elim H8; rewrite H4; apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 elim H3; trivial.
	 destruct (ProperAngle A B' C H7).
	   elim H6; rewrite <- H4; apply NullAngle; auto.
	 generalizeChange.
	 elim AS0diffASpi.
	   rewrite <- (NullAngle A B C); auto.
	   rewrite H4; apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 elim H3; trivial.
	 destruct (ProperAngle A B' C H7).
	   elim H8; rewrite <- H4; apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 elim AS0diffASpi.
	   rewrite <- (NullAngle A B' C); auto.
	   rewrite <- H4; apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 generalize (EquiOrientedSym A B' C H1 H6); generalizeChange.
Qed.

Lemma EqualAngleHalfLineC : forall A B C C' : Point,
	A <> B ->
	A <> C ->
	A <> C' ->
	~Clockwise A B C ->
	~Clockwise A B C' ->
	(Angle  C A B) = (Angle  C' A B) ->
	HalfLine A C C'.
Proof.
	intros.
	decompose [or] (ExclusiveFourCases A B C H0);
	 decompose [or] (ExclusiveFourCases A B C' H1).
	 elim H2; trivial.
	 elim H2; trivial.
	 elim H2; trivial.
	 elim H2; trivial.
	 elim H3; trivial.
	 apply (AngleBHalfLine A C B C'); auto.
	  autoClockwise.
	  autoClockwise.
	 destruct (ProperAngle A B C H6).
	   elim H7; rewrite AngleSym; auto.
	   rewrite H4; rewrite AngleSym; auto.
	   apply NullAngle; auto.
	 destruct (ProperAngle A B C H6).
	   elim H8; rewrite AngleSym; auto.
	   rewrite H4; rewrite AngleSym; auto.
	   apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 elim H3; trivial.
	 destruct (ProperAngle A B C' H7).
	   elim H6; rewrite AngleSym; auto.
	   rewrite <- H4; rewrite AngleSym; auto.
	   apply NullAngle; auto.
	 generalizeChange.
	 elim AS0diffASpi.
	   rewrite <- (NullAngle A B C); auto.
	   rewrite AngleSym; auto.
	   rewrite H4; rewrite AngleSym; auto.
	   apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 elim H3; trivial.
	 destruct (ProperAngle A B C' H7).
	   elim H8; rewrite AngleSym; auto.
	   rewrite <- H4; apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 elim AS0diffASpi.
	   rewrite <- (NullAngle A B C'); auto.
	   rewrite AngleSym; auto.
	   rewrite <- H4; rewrite AngleSym; auto.
	   apply ElongatedAngle; split; auto.
	   apply EquiOrientedSym; generalizeChangeSide.
	 generalize (EquiOrientedSym A B C' H H6); generalizeChange.
Qed.

End CONSEQUENCES.
