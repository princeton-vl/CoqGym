Require Export C9_Triangles_Emboites.

Section MIDPOINT.

Definition Middle (A B : Point) : Figure :=
fun I : Point => Collinear A B I /\ Distance I A = Distance I B.

Lemma DegeneratedMiddle : forall A : Point, Middle A A A.
Proof.
	intro A; split.
	 autoCollinear.
	 auto.
Qed.

Lemma ExistsMiddle : forall A B : Point,
	A <> B ->
	{I : Point | Middle A B I}.
Proof.
	intros A B H.
	destruct (EquilateralClockwise A B H) as (C, ((H1, H2), H3)).
	destruct (EquilateralClockwise B A (sym_not_eq H)) as (D, ((H4, H5), H6)).
	destruct (FourPointsIntersectionPoint A B C D H3 H6) as (I, (H7, H8)).
	exists I; split.
	 trivial.
	 apply (CongruentSAS C I A C I B).
	  autoDistinct.
	  autoDistinct.
	  auto.
	  rewrite DistSym; rewrite <- H1; rewrite H2; autoDistance.
	  rewrite (CongruentItself C I A D A).
	   rewrite (CongruentItself C I B D B).
	    apply CongruentSSS.
	     autoDistinct.
	     autoDistinct.
	     rewrite DistSym; rewrite <- H1; rewrite H2; autoDistance.
	     auto.
	     autoDistance.
	    autoDistinct.
	    autoDistinct.
	    apply BetweenHalfLine; trivial.
	    autoCollinear.
	   autoDistinct.
	   autoDistinct.
	   apply BetweenHalfLine; trivial.
	   autoCollinear.
Defined.

Definition MidPoint (A B : Point) : A <> B -> Point.
Proof.
	intros H; destruct (ExistsMiddle A B H) as (I, _); exact I.
Defined.

Lemma CollinearEquidistantBetween : forall A B I : Point,
	A <> B ->
	Collinear A B I ->
	Distance I A = Distance I B ->
	Between A I B.
Proof.
	intros.
	assert (I <> A).
	 intro; elim H; subst.
	   apply DistNull; autoDistance.
	 assert (I <> B).
	  intro; elim H; subst.
	    apply DistNull; autoDistance.
	  destruct (ExclusiveCollinear I A B H2 H3).
	   autoCollinear.
	   elim H; apply (HalfLineEquidistantEqual I A B H2 H4 H1).
	   apply BetweenSym; trivial.
Qed.

Lemma MidPointBetween : forall (A B : Point) (H : A <> B),
	Between A (MidPoint A B H) B.
Proof.
	intros; unfold MidPoint in |- *.
	destruct (ExistsMiddle A B H) as (I, (H1, H2)).
	apply CollinearEquidistantBetween; trivial.
Qed.

Lemma TwoMidPointsNotClockwise : forall A B C I J : Point,
	A <> B ->
	Between A I B ->
	Distance I A = Distance I B ->
	Between A J B ->
	Distance J A = Distance J B ->
	Clockwise A B C ->
	~Clockwise C I J.
Proof.
	red in |- *; intros.
	assert (H6 := BetweenClockwiseMBC A B C J H4 H2).
	assert (Between I J B).
	 apply (ClockwiseBetween I J B C).
	  autoClockwise.
	  autoClockwise.
	  apply CollinearBCA; apply (CollinearTrans B A I J).
	   auto.
	   apply CollinearCAB; apply BetweenCollinear; trivial.
	   apply CollinearCAB; apply BetweenCollinear; trivial.
	 destruct (ChaslesRec A J I).
	  rewrite (DistSym A J); rewrite H3.
	    rewrite (DistSym A I); rewrite H1.
	    rewrite (DistSym J B); rewrite (DistSym I B).
	    apply Chasles.
	   apply BetweenSymHalfLine; trivial.
	   apply BetweenHalfLine; trivial.
	  elim (ClockwiseNotClockwise A I C).
	   apply H8.
	     apply (EquiOrientedRev _ _ _ H2).
	     auto.
	   apply H9; autoClockwise.
Qed.

Lemma UniqueMidPoint : forall (A B : Point) (H : A <> B) (C : Point),
	Collinear A B C ->
	Distance C A = Distance C B ->
	C = MidPoint A B H.
Proof.
	intros A B H C H0 H1; unfold MidPoint in |- *.
	destruct (ExistsMiddle A B H) as (I, (H2, H3)).
	assert (H4 := CollinearEquidistantBetween A B C H H0 H1).
	assert (H5 := CollinearEquidistantBetween A B I H H2 H3).
	destruct (ClockwiseExists A B H) as (D, H6).
	decompose [or] (ThreeCases D C I).
	 elim (TwoMidPointsNotClockwise A B D C I H H4 H1 H5 H3 H6 H7).
	 elim (TwoMidPointsNotClockwise A B D I C H H5 H3 H4 H1 H6).
	   autoClockwise.
	 apply (UniqueIntersectionLines A B D C C I).
	  trivial.
	  intro; subst.
	    elim (ClockwiseNotCollinear _ _ _ H6); trivial.
	  apply FourPointsSecantLine.
	   trivial.
	   autoClockwise.
	  trivial.
	  trivial.
	  autoCollinear.
	  trivial.
Qed.

Lemma MidPointBetweenCD : forall (A B C D : Point) (H : A <> B),
	Distance C A = Distance C B ->
	Distance D A = Distance D B ->
	Clockwise A B C ->
	Clockwise B A D ->
	Between C (MidPoint A B H) D.
Proof.
	intros.
	destruct (FourPointsIntersectionPoint A B C D H2 H3) as (I, (H4, H5)).
	rewrite <- (UniqueMidPoint A B H I).
	 trivial.
	 trivial.
	 apply (CongruentSAS C I A C I B).
	  apply (BetweenDistinctAB _ _ _ H5).
	  autoDistinct.
	  trivial.
	  trivial.
	  rewrite (CongruentItself C I A D A).
	   rewrite (CongruentItself C I B D B).
	    apply CongruentSSS.
	     autoDistinct.
	     autoDistinct.
	     autoDistance.
	     autoDistance.
	     autoDistance.
	    autoDistinct.
	    autoDistinct.
	    apply BetweenHalfLine; auto.
	    canonize.
	   autoDistinct.
	   autoDistinct.
	   apply BetweenHalfLine; auto.
	   canonize.
Qed.

End MIDPOINT.
