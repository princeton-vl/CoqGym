Require Export E2_Ordre.

Section CONGRUENCE.

(* C1 : Given a line segment AB, and given a ray r originated at a point C, there exists a unique point D on the ray r such that AB = CD. *)

Lemma C1a : forall A B C D : Point,
	A <> B ->
	C <> D ->
	exists E : Point, HalfLine C D E /\ Distance A B = Distance C E.
Proof.
	intros.
	destruct (ExistsHalfLineEquidistant C D A B) as (E, (H1, H2)); auto.
	exists E; intuition.
Qed.

Lemma C1b : forall A B C D E F : Point,
	A <> B ->
	C <> D ->
	HalfLine C D E ->
	Distance A B = Distance C E ->
	HalfLine C D F ->
	Distance A B = Distance C F ->
	E = F.
Proof.
	intros.
	setLine C D H0 ipattern:(L) ipattern:(CD).
	setCircle C A B H ipattern:(G) ipattern:(CAB).
	setLinterposC L G CD CAB ipattern:(J) ipattern:(H5) ipattern:(H6) ipattern:(H7)
	 ipattern:(H8).
	 autoCollinear.
	 apply trans_eq with (y := J).
	  apply sym_eq; apply H8.
	    split.
	   apply HalfLineCollinear; trivial.
	   split.
	    autoDistance.
	    canonize.
	  apply H8; split.
	   apply HalfLineCollinear; trivial.
	   split.
	    autoDistance.
	    canonize.
Qed.

(* C2 : If AB = CD and AB = EF, then CD = EF. Every line segment is congruent to itself. *)

Lemma C2a : forall A B C D E F : Point,
	Distance A B = Distance C D ->
	Distance A B = Distance E F ->
	Distance C D = Distance E F.
Proof.
	intros A B C D E F H H0; rewrite <- H; auto.
Qed.

Lemma C2b : forall A B : Point,
	Distance A B = Distance A B.
Proof.
	auto.
Qed.

(* C3 : Given three points A, B, C on a line satisfying A - B - C, and three further points D, E, F on a line satisfying D - E - F, if AB = DE and BC = EF, then AC = DF. *)

Lemma C3 : forall A B C D E F : Point,
	Between A B C ->
	Between D E F ->
	Distance A B = Distance D E ->
	Distance B C = Distance E F ->
	Distance A C = Distance D F.
Proof.
	intros; rewrite <- (Chasles A B C).
	 rewrite H1; rewrite H2; apply Chasles; auto.
	  apply BetweenHalfLine; trivial.
	  apply BetweenSymHalfLine; trivial.
	 apply BetweenHalfLine; trivial.
	 apply BetweenSymHalfLine; trivial.
Qed.

(* C4 : Given an angle ^BAC and given a ray DF, there exists a unique ray DE on a given side of the line DF, such that ^BAC = ^EDF. *)

Lemma C4a : forall A B C D F : Point, 
	A <> B ->
	A <> C ->
	D <> F ->
	exists E : Point,
		D <> E /\
		~Clockwise D F E /\
		Angle B A C = Angle  E D F.
Proof.
	intros; decompose [or] (ExclusiveFourCases A B C H0).
	 destruct (ExistsHalfLineEquidistant D F A B H1 H) as (G, (H3, H4)).
	   destruct (EqualTriangleAntiClockwise A B C D G) as (E, (H5, (H6, H7)));
	    auto.
	   assert (H8 := ClockwiseDistinctAB D E G H5); exists E; intuition.
	  elim (ClockwiseNotClockwise D E G H5); apply ClockwiseCAB; canonize.
	  rewrite (CongruentItself D E F E G); canonize.
	    apply CongruentSSS; autoDistance.
	 destruct (ExistsHalfLineEquidistant D F A C H1 H0) as (G, (H2, H4)).
	   destruct (EqualTriangleAntiClockwise A C B D G) as (E, (H5, (H6, H7))).
	  autoClockwise.
	  auto.
	  assert (H8 := ClockwiseDistinctAB D E G H5); exists E; intuition.
	   elim (ClockwiseNotClockwise D E G H5); apply ClockwiseCAB; canonize.
	   rewrite (HalfLineAngleC D E F G); canonize.
	     apply CongruentSSS; autoDistance.
	 exists F; intuition.
	  autoClockwise.
	  rewrite (NullAngle D F F); canonize.
	    apply NullAngle; auto.
	 destruct (CentralSymetPoint F D (sym_not_eq H1)) as (E, (H3, H4)).
	   exists E; intuition.
	  elim (BetweenDistinctBC F D E H4); trivial.
	  elim (BetweenNotClockwiseBAC F D E H4); trivial.
	  rewrite (ElongatedAngle E D F (BetweenSym F D E H4)).
	    apply ElongatedAngle; split.
	   auto.
	   apply EquiOrientedSym; generalizeChangeSide.
Qed.

Lemma C4b : forall A B C D F : Point,
	A <> B ->
	A <> C ->
	D <> F ->
	exists E : Point,
		D <> E /\
		~Clockwise D E F /\
		Angle B A C = Angle  E D F.
Proof.
	intros; decompose [or] (ExclusiveFourCases A B C H0).
	 destruct (ExistsHalfLineEquidistant D F A B H1 H) as (G, (H3, H4)).
	   destruct (EqualTriangleClockwise A B C D G) as (E, (H5, (H6, H7))); auto.
	   assert (H8 := ClockwiseDistinctCA D G E H5); exists E; intuition.
	  generalizeChangeSense; elim (ClockwiseNotClockwise D G E H5).
	    apply H10; autoClockwise.
	  rewrite (CongruentItself D E F E G); canonize.
	    apply CongruentSSS; autoDistance.
	 destruct (ExistsHalfLineEquidistant D F A C H1 H0) as (G, (H2, H4)).
	   destruct (EqualTriangleClockwise A C B D G) as (E, (H5, (H6, H7))).
	  autoClockwise.
	  auto.
	  assert (H8 := ClockwiseDistinctCA D G E H5); exists E; intuition.
	   generalizeChangeSense; elim (ClockwiseNotClockwise D G E H5).
	     apply H10; autoClockwise.
	   rewrite (HalfLineAngleC D E F G); canonize.
	     apply CongruentSSS; autoDistance.
	 exists F; intuition.
	  autoClockwise.
	  rewrite (NullAngle D F F); canonize.
	    apply NullAngle; auto.
	 destruct (CentralSymetPoint F D (sym_not_eq H1)) as (E, (H3, H4)).
	   exists E; intuition.
	  elim (BetweenDistinctBC F D E H4); trivial.
	  elim (BetweenNotClockwiseABC F D E H4); autoClockwise.
	  rewrite (ElongatedAngle E D F (BetweenSym F D E H4)).
	    apply ElongatedAngle; split.
	   auto.
	   apply EquiOrientedSym; generalizeChangeSide.
Qed.

Lemma C4c : forall A B C D F E E' : Point,
	A <> B ->
	A <> C ->
	D <> F ->
	D <> E ->
	D <> E' ->
	~Clockwise D E F ->
	~Clockwise D E' F ->
	Angle B A C = Angle  E D F ->
	Angle B A C = Angle  E' D F ->
	Superimposed (HalfLine D E) (HalfLine D E').
Proof.
	intros.
	apply SuperimposedHalfLines; auto.
	apply (EqualAngleHalfLineB D E E' F); auto.
	rewrite <- H6; auto.
Qed.

Lemma C4d : forall A B C D F E E' : Point,
	A <> B ->
	A <> C ->
	D <> F ->
	D <> E ->
	D <> E' ->
	~Clockwise D F E ->
	~Clockwise D F E' ->
	(Angle B A C) = (Angle  E D F) ->
	(Angle B A C) = (Angle  E' D F) ->
	Superimposed (HalfLine D E) (HalfLine D E').
Proof.
	intros.
	apply SuperimposedHalfLines; auto.
	apply (EqualAngleHalfLineC D F E E'); auto.
	rewrite <- H6; auto.
Qed.

(* C5 : For any three angles ^A, ^B, ^C, if ^A = ^Bâ and ^A = ^C, then ^B = ^C. Every angle is congruent to itself. *)

Lemma C5a : forall A B C : Point,
	Angle B A C = Angle B A C.
Proof.
	trivial.
Qed.

Lemma C5b : forall A B C D E F G H J : Point,
	Angle B A C = Angle E D F ->
	Angle B A C = Angle H G J ->
	Angle E D F = Angle H G J.
Proof.
	intros.
	rewrite <- H0; trivial.
Qed.

(* C6 (SAS): Given triangles ABC and DEF, suppose that AB = DE and AC = DF and ^BAC = ^EDF, then the two triangles are congruent, namely, BC = EF, ^ABC = ^DEF and ^ACB = ^DFE. *)

Lemma C6a  : forall A B C D E F : Point,
	A <> B ->
	A <> C ->
	Distance A B = Distance D E ->
	Distance A C = Distance D F ->
	Angle B A C = Angle E D F ->
	Distance B C = Distance E F.
Proof.
	intros; apply (CongruentSAS A B C D E F); auto.
Qed.

Lemma C6b  : forall A B C D E F : Point,
	A <> B ->
	A <> C ->
	B <> C ->
	Distance A B = Distance D E ->
	Distance A C = Distance D F ->
	Angle B A C = Angle E D F ->
	Angle A B C = Angle D E F.
Proof.
	intros.
	apply CongruentSSS; auto.
	 rewrite (DistSym B A); rewrite (DistSym E D); trivial.
	 apply (CongruentSAS A B C D E F); auto.
Qed.

Lemma C6c  : forall A B C D E F : Point,
	A <> B ->
	A <> C ->
	B <> C ->
	Distance A B = Distance D E ->
	Distance A C = Distance D F ->
	Angle B A C = Angle E D F ->
	Angle A C B = Angle D F E.
Proof.
	intros.
	apply CongruentSSS; auto.
	 rewrite (DistSym C A); rewrite (DistSym F D); trivial.
	 rewrite (DistSym C B); rewrite (DistSym F E).
	   apply (CongruentSAS A B C D E F); auto.
Qed.

End CONGRUENCE.
