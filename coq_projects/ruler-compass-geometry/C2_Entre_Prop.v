Require Export C1_DemiDroite_Prop.

Section BETWEEN_PROPERTIES.

Lemma BetweenDistinctBC : forall A B C, Between A B C -> B <> C.
Proof.
	canonize; subst.
	destruct (ClockwiseExists A C H1) as (D, H3).
	assert (Clockwise C C D); [ auto | autoClockwise ].
Qed.

Lemma BetweenSym : forall A B C,
	Between A B C -> Between C B A.
Proof.
	split.
	 generalize (BetweenDistinctBC A B C); auto.
	 generalizeChange.
Qed.

Lemma BetweenCollinear : forall A B C,
	Between A B C -> Collinear A B C.
Proof.
	intros; apply HalfLineCollinear; apply BetweenHalfLine; trivial.
Qed.

Lemma BetweenDistinctCA : forall A B C, 
	Between A B C -> C <> A.
Proof.
	intros A B C H.
	generalize (BetweenHalfLine A B C H); canonize.
	destruct (ClockwiseExists A B H2) as (D, H4).
	elim (ClockwiseDistinctAB A C D); auto.
Qed.

Lemma HalfLineBetween : forall A B C,
	A <> B ->
	B <> C ->
	HalfLine A B C -> 
	HalfLine C B A -> 
	Between A B C.
Proof.
	generalizeChange.
Qed.

Lemma BetweenAssocLeft : forall A B C D : Point,
	Between A B C ->
	Between B C D ->
	Between A B D.
Proof.
	canonize.
	apply (BetweenHalfLine B C D); canonize.
Qed.

Lemma BetweenAssocRight : forall A B C D : Point,
	Between A B C ->
	Between B C D ->
	Between A C D.
Proof.
	canonize.
	 elim (BetweenDistinctCA A B C); canonize.
	 generalize (BetweenHalfLine A B C); generalizeChange.
Qed.

Lemma EquiOrientedCollinear : forall A B C,
	EquiOriented A B C A -> Collinear A B C.
Proof.
	generalizeChange.
	 elim (NotClockwiseABA C A); auto.
	 elim (NotClockwiseABA B A); apply H1.
	  autoDistinct.
	  autoClockwise.
Qed.

Lemma HalfLineEquiOrientedHalfLine : forall A B C D : Point,
	A <> B ->
	HalfLine A B C ->
	EquiOriented A B C D ->
	HalfLine A B D.
Proof.
	canonize.
	assert (Between A C D).
	 generalizeChange.
	   elim (ClockwiseDistinctAB A C x); auto.
	 generalize (BetweenHalfLine A C D H3); canonize.
Qed.

Lemma ClockwiseBetweenClockwise : forall A B C D E : Point,
	Clockwise A B C ->
	Between A D B ->
	Between A E C ->
	Clockwise A D E.
Proof.
	intros.
	generalize (BetweenHalfLine A D B H0); generalize (BetweenHalfLine A E C H1).
	generalizeChange.
	apply H9; apply ClockwiseBCA; apply H2; autoClockwise.
Qed.

Lemma NotCollinearBetweenNotCollinear : forall A B C D E : Point,
	~Collinear A B C ->
	Between A D B ->
	Between A E C ->
	~Collinear A D E.
Proof.
	canonize.
	elim H2; intros.
	 elim H1; apply (ClockwiseBetweenClockwise A B C D E); autoClockwise.
	 elim H6; apply ClockwiseCAB.
	   apply (ClockwiseBetweenClockwise A C B E D); autoClockwise.
Qed.

Lemma NotCollinearBetweenDistinct : forall A B C D E : Point,
	~Collinear A B C ->
	Between A D B ->
	Between A E C ->
	D <> E.
Proof.
	intros; apply (NotCollinearDistinctBC A D E).
	apply (NotCollinearBetweenNotCollinear A B C D E); auto.
Qed.

Lemma BetweenNotBetween : forall A B C : Point,
	Between A B C -> ~Between A C B.
Proof.
	intros A B C H; assert (H0 := BetweenHalfLine _ _ _ H).
	destruct (ClockwiseExists A B (BetweenDistinctAB _ _ _ H)) as (D, H1).
	intro H2; elim (ClockwiseNotClockwise _ _ _ H1).
	generalizeChange.
Qed.

Lemma ChaslesBetween : forall A B C : Point,
	Between A B C ->
	LSplus (Distance A B) (Distance B C) = Distance A C.
Proof.
	intros A B C H; apply Chasles.	
	 apply BetweenHalfLine; trivial.
	 apply BetweenSymHalfLine; trivial.
Qed.

Lemma HalfLineEquidistantEqualPoints : forall A B C D E : Point, forall d : LS,
	HalfLine A C B ->
	Distance A C = d ->
	HalfLine A B D ->
	A <> C ->	
	Distance A D = LSplus (Distance A B) d ->
	Between A C E ->
	Distance C E = Distance A B ->
 	E = D.
Proof.
	intros.
	apply (HalfLineEquidistantEqual A).
	 exact (sym_not_eq (BetweenDistinctCA _ _ _ H4)).
	 assert (HalfLine A E C).
	  apply (HalfLineSym A C E H2 (BetweenHalfLine _ _ _ H4)).
	  canonize.
	 rewrite (DistSym A E).
	   rewrite <- (ChaslesBetween _ _ _ (BetweenSym _ _ _ H4)).
	   autoDistance.
	   rewrite (DistSym C A); rewrite H0; auto.
Qed.

End BETWEEN_PROPERTIES.
