Require Export B10_Longueur_Prop.

Section ANGLE_PROPERTIES.

Lemma AngleSym : forall A B C : Point, 
	A <> B ->
	A <> C ->
	Angle B A C = Angle C A B.
Proof.
	intros; apply CongruentItself; canonize.
Qed.

Lemma HalfLineAngleB : forall A B C D : Point,
	A <> B ->
	A <> C ->
	HalfLine A B D ->
	Angle B A C = Angle D A C.
Proof.
	intros; rewrite AngleSym; auto.
	apply CongruentItself; canonize.
Qed.

Lemma HalfLineAngleC : forall A B C D : Point,
	A <> B ->
	A <> C ->
	HalfLine A C D ->
	Angle B A C = Angle B A D.
Proof.
	intros; rewrite AngleSym; auto.
	apply CongruentItself; canonize.
Qed.

Lemma HalfLineAngleBC : forall A B C D E : Point,
	A <> B ->
	A <> C ->
	HalfLine A B D ->
	HalfLine A C E ->
	Angle B A C = Angle D A E.
Proof.
	intros; rewrite AngleSym; auto.
	apply CongruentItself; canonize.
Qed.

Lemma BetweenAngleBC : forall A B C D E : Point,
  	Between A B D -> 
	Between A C E -> 
	Angle B A C = Angle D A E.
Proof.
	intros; apply HalfLineAngleBC.
	 apply (BetweenDistinctAB _ _ _ H).	
	 apply (BetweenDistinctAB _ _ _ H0).
	 apply (BetweenHalfLine _ _ _ H).
	 apply (BetweenHalfLine _ _ _ H0).
Qed.

Lemma BetweenAngleC : forall A B C D : Point,
  	A <> B ->
	Between A C D -> 
	Angle B A C = Angle B A D.
Proof.
	intros; apply HalfLineAngleC.
	 trivial.
	 apply (BetweenDistinctAB _ _ _ H0).
	 apply (BetweenHalfLine _ _ _ H0).
Qed.

Lemma BetweenAngleB : forall A B C D : Point,
	A <> C ->
  	Between A B D -> 
	Angle B A C = Angle D A C.
Proof.
	intros; apply HalfLineAngleB.
	 apply (BetweenDistinctAB _ _ _ H0).
	 trivial.
	 apply (BetweenHalfLine _ _ _ H0).
Qed.

Lemma SASEqualBD : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise A D C ->
	Distance A B = Distance A D ->
	Angle B A C = Angle D A C ->
	B = D.
Proof.
	intros; apply (SSSEqualBD A B C D); auto.
	apply (CongruentSAS A B C A D C); auto.
	 exact (ClockwiseDistinctAB A B C H).
	 exact (sym_not_eq (ClockwiseDistinctCA A B C H)).
Qed.

Lemma SASEqualCD : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise A B D ->
	Distance A C = Distance A D ->
	Angle B A C = Angle B A D ->
	C = D.
Proof.
	intros; apply (SSSEqualCD A B C D); auto.
	apply (CongruentSAS A B C A B D); auto.
	 exact (ClockwiseDistinctAB A B C H).
	 exact (sym_not_eq (ClockwiseDistinctCA A B C H)).
Qed.

Lemma AngleBHalfLine : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise A D C ->
	Angle B A C = Angle D A C ->
	HalfLine A B D.
Proof.
	intros.
	assert (Hab := ClockwiseDistinctAB A B C H).
	assert (Had := ClockwiseDistinctAB A D C H0).
	destruct (ExistsHalfLineEquidistant A B A D Hab Had) as (E, (H2, H3)).
	rewrite (SASEqualBD A D C E H0).
	 trivial.
	 canonize.
	 auto.
	 rewrite <- H1; apply HalfLineAngleB; auto.
	   exact (sym_not_eq (ClockwiseDistinctCA A B C H)).
Qed.

Lemma AngleCHalfLine : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise A B D ->
	Angle B A C = Angle B A D ->
	HalfLine A C D.
Proof.
	intros.
	assert (Hac := sym_not_eq (ClockwiseDistinctCA A B C H)).
	assert (Had := sym_not_eq (ClockwiseDistinctCA A B D H0)).
	destruct (ExistsHalfLineEquidistant A C A D Hac Had) as (E, (H2, H3)).
	rewrite (SASEqualCD A B D E H0).
	 trivial.
	 generalizeChangeSense.
	   apply ClockwiseBCA; apply H4; apply ClockwiseCAB; trivial.
	 auto.
	 rewrite <- (HalfLineAngleC A B C E); auto.
	   exact (ClockwiseDistinctAB A B C H).
Qed.

End ANGLE_PROPERTIES.

Section PARTICULAR_ANGLES.

Definition AS0 := Angle Uu Oo Uu.

Definition Ww : Point.
Proof.
	destruct (CentralSymetPoint Uu Oo (sym_not_eq DistinctOoUu)) as (x,_).
	exact x.
Defined.

Lemma DistOoWw : Distance Uu Oo = Distance Oo Ww.
Proof.
	unfold Ww; destruct (CentralSymetPoint Uu Oo (sym_not_eq DistinctOoUu)).
	intuition.
Qed.

Lemma DistinctOoWw : Oo <> Ww.
Proof.
	apply (EquiDistantDistinct Oo Uu Oo Ww DistinctOoUu).
	rewrite <- DistOoWw; apply DistSym.
Qed.

Lemma BetweenUuOoWw : Between Uu Oo  Ww.
Proof.
	unfold Ww; destruct (CentralSymetPoint Uu Oo (sym_not_eq DistinctOoUu)).
	intuition.
Qed.

Lemma BetweenWwOoUu : Between Ww Oo  Uu.
Proof.
	assert (H := BetweenUuOoWw).
	generalizeChange.
	destruct (ClockwiseExists Uu Oo H0) as (V, H4).
	elim (ClockwiseDistinctAB Oo Ww V); auto.
Qed.

Definition ASpi := Angle Uu Oo Ww.

Lemma NullAngle : forall A B C : Point, 
	A <> B ->
	HalfLine A B C -> 
	Angle B A C = AS0.
Proof.
	intros; unfold AS0 in |- *.
	destruct (ExistsHalfLineEquidistant A B Oo Uu H DistinctOoUu) as (D, (H1, H2)).
	rewrite (CongruentItself A B C D D H).
	 assert (H3 := EquiDistantDistinct Oo Uu A D DistinctOoUu (sym_eq H2)).
	   apply CongruentSSS; auto.
	   exact (DistAA D Uu).
	 canonize.
	   destruct (ClockwiseExists A B H) as (E, H4).
	   elim (ClockwiseDistinctAB A C E); auto.
	 trivial.
	 generalizeChange.
Qed.

Lemma ElongatedAngle : forall A B C : Point, 
	Between A B C -> 
	Angle A B C = ASpi.
Proof.
	intros; unfold ASpi in |- *.
	assert (H0 : B <> A).
	 canonize.
	 assert (H1 : B <> C).
	  canonize.
	    destruct (ClockwiseExists A B H2) as (D, H4).
	    elim (ClockwiseDistinctAB B C D); auto.
	  destruct (ExistsHalfLineEquidistant B A Oo Ww H0 DistinctOoWw)
	   as (D, (H2, H3)).
	    destruct (ExistsHalfLineEquidistant B C Oo Uu H1 DistinctOoUu)
	     as (E, (H4, H5)).
	    rewrite (CongruentItself B A C D E H0 H1 H2 H4).
	    apply CongruentSSS; auto.
	   canonize.
	     destruct (ClockwiseExists B C H1) as (F, H9).
	     elim (ClockwiseDistinctAB B E F); auto.
	   canonize.
	     destruct (ClockwiseExists B A H0) as (F, H9).
	     elim (ClockwiseDistinctAB B D F); auto.
	   rewrite <- (Chasles E B D).
	    rewrite (DistSym E B); rewrite H5; rewrite (DistSym Oo Uu).
	      rewrite H3; apply Chasles.
	     apply BetweenHalfLine; apply BetweenUuOoWw.
	     apply BetweenHalfLine; apply BetweenWwOoUu.
	    apply BetweenHalfLine; generalizeChange.
	      destruct (ClockwiseExists B C H1) as (F, H16).
	      elim (ClockwiseDistinctAB B E F); auto.
	    apply BetweenHalfLine; generalizeChange.
	      destruct (ClockwiseExists A B H6) as (F, H16).
	      elim (ClockwiseDistinctAB D B F); auto.
 Qed.

Lemma NullAngleHalfLine : forall A B C : Point, 
		A <> B ->
		A <> C ->
		Angle B A C = AS0 ->
		HalfLine A B C.
Proof.
	intros.
	destruct (ExistsHalfLineEquidistant A B A C H H0) as (D, (H2, H3)).
	rewrite (DistNull C D).
	 trivial.
	 rewrite <- (NullDist C).
	   apply (CongruentSAS A C D A C C); auto.
	  apply (EquiDistantDistinct A C A D); auto.
	  rewrite <- (HalfLineAngleC A C B D); auto.
	    rewrite <- (AngleSym A B C); auto.
	    rewrite (NullAngle A C C); auto.
	    canonize.
Qed.

Lemma ElongatedAngleChasles : forall A B C : Point, 
		A <> B ->
		A <> C ->
		Angle B A C = ASpi ->
		LSplus (Distance B A) (Distance A C) = Distance B C.
Proof.
	intros.
	destruct (ExistsBetweenEquidistant A C A B H0 H) as (D, (H2, H3)).
	rewrite (DistSym B A); rewrite <- H3; rewrite (DistSym A D).
	apply trans_eq with (y := Distance D C).
	 apply Chasles.
	  apply BetweenHalfLine; trivial.
	  apply BetweenSymHalfLine; trivial.
	 apply sym_eq; apply (CongruentSAS A B C A D C); auto.
	   rewrite (ElongatedAngle D A C); auto.
Qed.

Lemma ElongatedAngleRec : forall A B C : Point,
	A <> B ->
	A <> C ->
	Angle B A C = ASpi ->
	Between B A C.
Proof.
	intros.
	assert (H2 := ElongatedAngleChasles A B C H H0 H1).
	destruct (ChaslesRec _ _ _ H2).
	generalizeChange.
Qed.

End PARTICULAR_ANGLES.
