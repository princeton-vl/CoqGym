Require Export C15_Parallelogramm.

Section DISTANCE_PROPERTIES.

Lemma LSltNotRefl : forall A B : Point,
	~LSlt (Distance A B) (Distance A B).
Proof.
	intros A B H.
	elim (LSltOrder A B B).
	 intuition.
	 canonize.
	 trivial.
Qed.

Lemma LSltNotEq : forall A B C D, 
	LSlt (Distance A B) (Distance C D) -> 
	(Distance A B) <> (Distance C D).
Proof.
	intros A B C D H0 H1; rewrite <- H1 in H0.
	elim (LSltNotRefl A B); auto.
Qed.

Lemma LSplusComm : forall A B C D : Point,
	A <> B ->
	C <> D ->
	LSplus (Distance A B) (Distance C D) = LSplus (Distance C D) (Distance A B).
Proof.
	intros.
	destruct (ExistsBetweenEquidistant B A C D) as (E, (H1, H2)); auto.
	rewrite <- H2.
	apply ChaslesComm.
	 exact (BetweenSymHalfLine _ _ _ H1).
	 exact (BetweenHalfLine _ _ _ H1).
Qed.

Lemma LSplusAss : forall A B C D E F : Point,
	A <> B ->
	C <> D ->
	E <> F ->
	LSplus (Distance A B) (LSplus (Distance C D) (Distance E F)) = 
		LSplus(LSplus (Distance A B)  (Distance C D)) (Distance E F).
Proof.
	intros.
	destruct (ExistsBetweenEquidistant B A C D) as (G, (H2, H3)); auto.
	destruct (ExistsBetweenEquidistant G B E F) as (J, (H4, H5)); auto.
	 autoDistinct.
	 rewrite <- H3; rewrite <- H5.
	   apply ChaslesAssoc.
	  apply BetweenSymHalfLine; trivial.
	  apply BetweenHalfLine; trivial.
	  apply BetweenSymHalfLine; apply (BetweenAssocRight J G B A H4 H2).
	  apply BetweenHalfLine; apply (BetweenAssocRight J G B A H4 H2).
	  apply BetweenSymHalfLine; trivial.
	  apply BetweenHalfLine; trivial.
	  apply BetweenSymHalfLine; apply (BetweenAssocLeft J G B A H4 H2).
	  apply BetweenHalfLine; apply (BetweenAssocLeft J G B A H4 H2).
Qed.

Lemma LSltLSplus : forall A B C D : Point,
	LSlt LS0 (Distance A B) ->
	LSlt LS0 (Distance C D) ->
	LSlt LS0 (LSplus (Distance A B) (Distance C D)).
Proof.
	intros A B C D H H0.
	assert (H1 := LSltNull A B H); assert (H2 := LSltNull C D H0).
	destruct (ExistsEquidistantBetween A B C D H1 H2) as (E, (H3, H4)).
	rewrite <- H4; rewrite Chasles; auto.
	 apply NullLSlt; apply (BetweenDistinctCA E B A); apply BetweenSym; trivial.
	 apply BetweenHalfLine; trivial.
	 apply BetweenSymHalfLine; trivial.
Qed.

Lemma ChaslesLSltTrans : forall A B C D : Point,
	A <> B ->
	HalfLine A B C ->
	HalfLine A C D ->
	LSlt (Distance A B) (Distance A C) ->
	LSlt (Distance A C) (Distance A D) ->
		LSlt (Distance A B) (Distance A D).
Proof.
	intros; apply BetweenLSlt.
	apply (BetweenTransA A B C D).
	 apply LSltBetween; auto.
	 apply LSltBetween; auto.
	   apply sym_not_eq; apply (BetweenDistinctCA A B C).
	   apply LSltBetween; auto.
Qed.

Lemma LSltTrans : forall A B C D E F : Point,
	A <> B ->
	C <> D ->
	E <> F ->
	LSlt (Distance A B) (Distance C D) ->
	LSlt (Distance C D) (Distance E F) ->
	LSlt (Distance A B) (Distance E F).
Proof.
	intros.
	destruct (ExistsHalfLineEquidistant A B C D) as (G, (H4, H5)); auto.
	destruct (ExistsHalfLineEquidistant A B E F) as (J, (H6, H7)); auto.
	rewrite <- H7; apply (ChaslesLSltTrans A B G J); auto.
	 generalizeChange.
	 rewrite H5; trivial.
	 rewrite H5; rewrite H7; trivial.
Qed.

End DISTANCE_PROPERTIES.
