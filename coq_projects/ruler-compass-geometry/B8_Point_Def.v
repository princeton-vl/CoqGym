Require Export B7_Triangle_Equilateral.

Section POINT_PROPERTIES.

Lemma ExistsHalfLineEquidistant : forall A B C D : Point,
	A <> B ->
	C <> D ->
	{E : Point |
		HalfLine A B E /\
		Distance A E = Distance C D}.
Proof.
	intros A B C D Hab Hcd.
	setLine A B Hab ipattern:(L) ipattern:(AB).
	setCircle A C D Hcd ipattern:(G) ipattern:(ACD).
	setLinterposC L G AB ACD ipattern:(E) ipattern:(H1) ipattern:(H2) ipattern:(H3) ipattern:(H4).
	 apply CollinearABA.
	 exists E; canonize.
Qed.

Lemma HalfLineEquidistantEqual : forall A B C : Point,
	A <> B ->
	HalfLine A B C ->
	Distance A B = Distance A C ->
	B = C.
Proof.
	intros.
	setLine A B H ipattern:(L) ipattern:(AB).
	setCircle A A B H ipattern:(G) ipattern:(Aab).
	setLinterposC L G AB Aab ipattern:(D) ipattern:(H2) ipattern:(H3) ipattern:(H4) ipattern:(H5).
	 apply CollinearABA.
	 rewrite <- (H5 B).
	  apply H5.
	    canonize.
	   elim (NotClockwiseBAA C A); auto.
	   generalizeChangeSense.
	     elim (NotClockwiseABA C A); auto.
	  canonize.
	   exact (NotClockwiseBAA B A H2).
	   exact (NotClockwiseABA B A H2).
Qed.

Lemma ExistsBetweenEquidistant : forall A B C D : Point,
	A <> B ->
	C <> D ->
	{E : Point |
		Between E A B /\
		Distance A E = Distance C D}.
Proof.
	intros A B C D Hab Hcd.
	setLine A B Hab ipattern:(L) ipattern:(AB).
	setCircle A C D Hcd ipattern:(G) ipattern:(ACD).
	setLinternegC L G AB ACD ipattern:(E) ipattern:(H1) ipattern:(H2) ipattern:(H3) ipattern:(H4).
	 apply CollinearABA.
	 exists E; canonize.
	  destruct (ClockwiseExists B A (sym_not_eq Hab)) as (F, H5).
	    subst; elim (NotClockwiseAAB A F); auto.
	  generalizeChangeSide.
Qed.

Lemma ExistsEquidistantBetween : forall A B C D : Point,
	A <> B ->
	C <> D ->
	{E : Point |
		Between A B E  /\
		Distance B E = Distance C D}.
Proof.
	intros A B C D Hab Hcd.
	setLine A B Hab ipattern:(L) ipattern:(AB).
	setCircle B C D Hcd ipattern:(G) ipattern:(BCD).
	setLinterposC L G AB BCD ipattern:(E) ipattern:(H1) ipattern:(H2) ipattern:(H3)
	 ipattern:(H4).
	 apply CollinearABB.
	 exists E; canonize.
Qed.

Lemma CentralSymetPoint : forall A B : Point,
	A <> B ->
	{C : Point | Distance A B = Distance B C /\ Between A B C}.
Proof.
	intros.
	destruct (ExistsBetweenEquidistant B A A B (sym_not_eq H) H) as (C, (H0, H1)).
	exists C; generalizeChangeSide.
Qed.

Lemma CoordinatePoint : forall A B : Point,
	A <> B ->
	{C : Point | HalfLine Oo Uu C /\ Distance Oo C = Distance A B}.
Proof.
	intros.
	exact (ExistsHalfLineEquidistant Oo Uu A B DistinctOoUu H).
Qed.

End POINT_PROPERTIES.
