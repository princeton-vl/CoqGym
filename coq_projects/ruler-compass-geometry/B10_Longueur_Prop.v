Require Export B9_Inegalite_Triang.

Section METRIC_BASICS.

Definition LS0 := Distance Oo Oo.

Lemma NullDist : forall A, 
	Distance A A = LS0.
Proof.
	intro; unfold LS0 in |- *; apply DistAA.
Qed.

Lemma NullLSlt : forall A B : Point, 
	A <> B -> LSlt LS0 (Distance A B).
Proof.
	intros; rewrite <- (NullDist A).
	apply OrderLSlt; auto.
	canonize.
	elim (NotClockwiseAAB _ _ H0).
Qed.

Lemma EquiOrientedNotEquiOriented : forall A B C D : Point,
	A <> B ->
	EquiOriented A B C D ->
	~EquiOriented A B D C.
Proof.
	canonize.
	destruct (ClockwiseExists A B H) as (E, H2).
	elim (ClockwiseNotClockwise C D E); auto.
Qed.

Lemma LSltDistinct : forall A B C D, 
	LSlt (Distance A B) (Distance C D) -> C <> D.
Proof.
	red in |- *; intros; subst.
	rewrite (DistAA D A) in H.
	destruct (LSltOrder A B A).
	 right; canonize.
	   elim (NotClockwiseAAB A x); auto.
	 trivial.
	 elim (EquiOrientedNotEquiOriented A B B A (sym_not_eq H1) H0).
	   canonize.
Qed.

Lemma LSltNull : forall A B, 
	LSlt LS0 (Distance A B) -> A <> B.
Proof.
	red in |- *; intros; subst.
	rewrite <- (NullDist B) in H.
	destruct (LSltOrder B B B).
	 canonize.
	 trivial.
	 auto.
Qed.

Lemma NotLSltNullNull : ~LSlt LS0 LS0.
Proof.
	change (~ LSlt LS0 (Distance Oo Oo)) in |- *.
	intro.
	elim (LSltNull _ _ H).
	trivial.
Qed.

Lemma LS0NeutralRight : forall A B : Point,
	LSplus (Distance A B) LS0 = Distance A B.
Proof.
	intros.
	rewrite <- (NullDist B); rewrite Chasles; canonize.
	elim (NotClockwiseAAB B x); trivial.
Qed.

Lemma LS0NeutralLeft : forall A B : Point,
	LSplus LS0 (Distance A B) = Distance A B.
Proof.
	intros.
	rewrite <- (NullDist A); rewrite Chasles; canonize.
	elim (NotClockwiseAAB A x); trivial.
Qed.

Lemma EquiOrientedNotEquiOrientedABC : forall A B C : Point,
	A <> B ->
	EquiOriented A B B C ->
	~EquiOriented A C C B.
Proof.
	canonize.
	destruct (ClockwiseExists A B H) as (E, H2).
	decompose [or] (FourCases A B C).
	 elim (NotClockwiseBAA C B); auto.
	 elim (NotClockwiseBAA B C); apply H1; apply ClockwiseBCA; trivial.
	 canonize.
	   elim (ClockwiseNotClockwise B C E); auto.
	 generalizeChangeSense.
	   elim (ClockwiseNotClockwise B C E); auto.
Qed.

Lemma HalfLineAntisymLSlt  : forall A B C : Point,
	A <> B ->
	HalfLine A B C ->
	LSlt (Distance A B) (Distance A C) ->
	~LSlt (Distance A C) (Distance A B).
Proof.
	red in |- *; intros.
	assert (H3 : HalfLine A B C \/ HalfLine A C B).
	 intuition.
	 destruct (LSltOrder _ _ _ H3 H1).
	   elim (EquiOrientedNotEquiOrientedABC _ _ _ H H4).
	   assert (EquiOriented A C C B /\ C <> B).
	  apply LSltOrder.
	   generalizeChange.
	   trivial.
	  intuition.
Qed.

Lemma AntisymLSlt  : forall A B C : Point,
	A <> B ->
	LSlt (Distance A B) (Distance A C) ->
	~LSlt (Distance A C) (Distance A B).
Proof.
	intros.
	assert (H1 := LSltDistinct _ _ _ _ H0).
	destruct (ExistsHalfLineEquidistant A B A C H H1) as (D, (H2, H3)).
	rewrite <- H3; rewrite <- H3 in H0.
	apply HalfLineAntisymLSlt; auto.
Qed.

Lemma ClockwiseNotNullSide : forall A B C : Point,
	Clockwise A B C ->
	~Distance B C = LS0.
Proof.
	red in |- *; intros.
	assert (H1 := TriangularIneq _ _ _ H).
	rewrite H0 in H1; rewrite LS0NeutralRight in H1.
	elim (AntisymLSlt A C B).
	 apply sym_not_eq; apply (ClockwiseDistinctCA _ _ _ H).
	 trivial.
	 assert (H2 := TriangularIneq _ _ _ (ClockwiseBCA _ _ _ H)).
	   rewrite H0 in H2; rewrite LS0NeutralLeft in H2.
	   rewrite (DistSym A B); rewrite (DistSym A C); trivial.
Qed.

Lemma DistDistinctNull : forall A B D : Point, 
	Distance A B = LS0 -> 
	D <> A ->
	A = B.
Proof.
	intros.
	decompose [or] (FourCases D A B).
	 elim (ClockwiseNotNullSide _ _ _ H1); trivial.
	 elim (ClockwiseNotNullSide _ _ _ (ClockwiseBCA _ _ _ H2)); rewrite DistSym;
	  trivial.
	 decompose [or] (FourCases B A D).
	  elim (ClockwiseNotNullSide _ _ _ (ClockwiseCAB _ _ _ H2)); rewrite DistSym;
	   trivial.
	  elim (ClockwiseNotNullSide _ _ _ (ClockwiseCAB _ _ _ H3)); trivial.
	  apply (HalfLineEquidistantEqual D A B H0 H1).
	    rewrite <- (Chasles D A B H1 H2).
	    rewrite H; rewrite LS0NeutralRight; trivial.
	  assert (H3 : HalfLine D B A).
	   generalizeChange.
	   assert (H4 : D <> B).
	    canonize; subst.
	      destruct (ClockwiseExists B A H0) as (C, H4).
	      elim (NotClockwiseAAB B C); auto.
	    apply sym_eq; apply (HalfLineEquidistantEqual D B A H4 H3).
	      rewrite <- (Chasles D B A H3 H2).
	      rewrite (DistSym B A); rewrite H; rewrite LS0NeutralRight; trivial.
	 assert (H2 : A <> B).
	  intro; subst; canonize.
	    destruct (ClockwiseExists B D (sym_not_eq H0)) as (C, H2).
	    elim (NotClockwiseAAB B C); auto.
	  elim NotLSltNullNull.
	    pattern LS0 at 2 in |- *; rewrite <- H.
	    apply NullLSlt; trivial.
Qed.

Lemma DistNull : forall A B, 
	Distance A B = LS0 -> A = B.
Proof.
	intros; destruct (Apart Oo Uu A DistinctOoUu).
	 apply (DistDistinctNull A B Oo); auto.
	 apply (DistDistinctNull A B Uu); auto.
Qed.

Lemma EquiDistantDistinct : forall A B C D : Point,
	A <> B ->
	Distance A B = Distance C D ->
	C <> D.
Proof.
	intuition; subst.
	elim H; apply DistNull.
	rewrite H0; apply NullDist.
Qed.

Lemma BetweenLSlt : forall A B C, 
	(Between A B C) -> 
	LSlt (Distance A B) (Distance A C).
Proof.
	intros.
	apply OrderLSlt; canonize.
	destruct (ClockwiseExists A B H1) as (D, H3).
	elim (ClockwiseDistinctAB B C D); auto.
Qed.

Lemma LSltBetween : forall A B C, 
	A <> B ->
	HalfLine A B C ->
	LSlt (Distance A B) (Distance A C) ->
	(Between A B C).
Proof.
	intros.
	assert (H2 : EquiOriented A B B C /\ B <> C).
	 apply (LSltOrder A B C); intuition.
	 canonize.
Qed.

Lemma DistDistinct : forall A B, 
	Distance A B <> LS0 -> A <> B.
Proof.
	intuition.
	subst; elim H; apply NullDist.
Qed.

Lemma DistinctDist : forall A B, 
	A <> B -> Distance A B <> LS0.
Proof.
	intuition.
	elim H; apply DistNull; auto.
Qed.

End METRIC_BASICS.

Section METRIC_PROPERTIES.

Lemma ChaslesComm : forall A B C : Point,
	HalfLine A B C ->
	HalfLine C B A -> 
	LSplus (Distance A B) (Distance B C) = LSplus (Distance B C) (Distance A B).
Proof.
	intros A B C H H0.
	rewrite (Chasles A B C H H0).
	rewrite (DistSym B C); rewrite (DistSym A B); rewrite (Chasles C B A H0 H).
	apply DistSym.
Qed.

Lemma ChaslesAssoc : forall A B C D : Point,
	HalfLine A B C ->
	HalfLine C B A -> 
	HalfLine A B D ->
	HalfLine D B A -> 
	HalfLine B C D ->
	HalfLine D C B -> 
	HalfLine A C D ->
	HalfLine D C A -> 
	LSplus (Distance A B) (LSplus (Distance B C) (Distance C D)) = 
		LSplus (LSplus (Distance A B) (Distance B C)) (Distance C D).
Proof.
	intros.
	repeat (rewrite Chasles; auto).
Qed.

Lemma SSSEqualBD : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise A D C ->
	Distance A B = Distance A D ->
	Distance B C = Distance D C ->
	B = D.
Proof.
	intros.
	assert (Hab := ClockwiseDistinctAB A B C H).
	assert (Hbc := ClockwiseDistinctBC A B C H).
	setCircle A A B Hab ipattern:(G1) ipattern:(Aab).
	setCircle C B C Hbc ipattern:(G2) ipattern:(Cbc).
	setCinterantiC G1 G2 Aab Cbc ipattern:(E) ipattern:(H3) ipattern:(H4) ipattern:(H5)
	 ipattern:(H6).
	 rewrite (DistSym A C); apply ClockwiseTriangleSpec; apply ClockwiseCAB; auto.
	 rewrite <- (H6 B).
	  apply H6.
	    intuition.
	   rewrite (DistSym C D); auto.
	   apply ClockwiseCAB; auto.
	  intuition.
	   rewrite (DistSym C B); auto.
	   apply ClockwiseCAB; auto.
Qed.

Lemma SSSEqualCD : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise A B D ->
	Distance A C = Distance A D ->
	Distance B C = Distance B D ->
	C = D.
Proof.
	intros.
	assert (Hac := sym_not_eq (ClockwiseDistinctCA A B C H)).
	assert (Hbc := ClockwiseDistinctBC A B C H).
	setCircle A A C Hac ipattern:(G1) ipattern:(Aac).
	setCircle B B C Hbc ipattern:(G2) ipattern:(Bbc).
	setCinterantiC G2 G1 Bbc Aac ipattern:(E) ipattern:(H3) ipattern:(H4) ipattern:(H5)
	 ipattern:(H6).
	 rewrite (DistSym B A); rewrite (DistSym A C); apply ClockwiseTriangleSpec;
	  auto.
	 rewrite <- (H6 C).
	  apply H6.
	    intuition.
	  intuition.
Qed.

End METRIC_PROPERTIES.
