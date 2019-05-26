Require Export C11_Mediatrice.

Section OPPOSED_ANGLE.

Lemma BetweenHalfLineBetween : forall A B C D : Point,
	Between A B C ->
	HalfLine B C D ->
	Between A B D.
Proof.
	intros.
	autoClockwise.
Qed.

Lemma CongruentOppParallelogramm : forall A B C D E : Point, 
		Between B A D -> 
		Between C A E ->
		Distance A B = Distance A C ->
		Distance A B = Distance A D ->
		Distance A B = Distance A E ->
		~Collinear A B C ->
		Angle B A C = Angle E A D.
Proof.
	intros.
	apply CongruentStrictTrianglesA; repeat split.
	 trivial.
	 apply (CongruentStrictTrianglesCA C D B D C E).
	   apply CongruentStrictTrianglesSASB.
	  autoDistance.
	  rewrite <- (Chasles D A B).
	   rewrite <- (Chasles C A E).
	    rewrite (DistSym D A); rewrite (DistSym C A).
	      rewrite <- H1; rewrite <- H2; autoDistance.
	    apply BetweenHalfLine; trivial.
	    apply BetweenSymHalfLine; trivial.
	   apply BetweenSymHalfLine; trivial.
	   apply BetweenHalfLine; trivial.
	  assert (H5 : C <> D).
	   intro; elim H4; subst.
	     apply CollinearBAC; apply BetweenCollinear; trivial.
	   rewrite (CongruentItself D C B C A).
	    rewrite (CongruentItself C D E D A).
	     apply CongruentStrictTrianglesB; repeat split.
	      autoDistance.
	      autoDistance.
	      rewrite (DistSym C A); rewrite <- H1; rewrite H2; autoDistance.
	      intro; elim H4; apply (CollinearTrans A D B C).
	       apply (BetweenDistinctBC _ _ _ H).
	       apply CollinearBCA; apply BetweenCollinear; trivial.
	       trivial.
	     trivial.
	     apply sym_not_eq; apply (BetweenDistinctCA _ _ _ H0).
	     canonize.
	     apply HalfLineSym.
	      apply (BetweenDistinctAB _ _ _ H0).
	      apply BetweenHalfLine; trivial.
	    auto.
	    apply (BetweenDistinctCA _ _ _ H).
	    canonize.
	    apply HalfLineSym.
	     apply sym_not_eq; apply (BetweenDistinctBC _ _ _ H).
	     apply BetweenHalfLine; apply BetweenSym; auto.
	  intro; elim H4; apply CollinearBAC; apply (CollinearTrans B D A C).
	   apply sym_not_eq; apply (BetweenDistinctCA _ _ _ H).
	   apply CollinearACB; apply BetweenCollinear; trivial.
	   autoCollinear.
	 rewrite (DistSym C A); rewrite <- H1; rewrite H2; autoDistance.
	 trivial.
 Qed.

Lemma CongruentOpp : forall A B C D E : Point, 
		Between B A D -> 
		Between C A E ->
		~Collinear A B C ->
		Angle B A C = Angle E A D.
Proof.
	intros.
	assert (A <> B).
	 apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H).
	 assert (A <> C).
	  apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H0).
	  assert (A <> D).
	   apply (BetweenDistinctBC _ _ _ H).
	   assert (A <> E).
	    apply (BetweenDistinctBC _ _ _ H0).
	    destruct (ExistsHalfLineEquidistant A B A C H2 H3) as (B', (H6, H7)).
	      destruct (ExistsHalfLineEquidistant A D A C H4 H3) as (D', (H8, H9)).
	      destruct (ExistsHalfLineEquidistant A E A C H5 H3) as (E', (H10, H11)).
	      rewrite (CongruentItself A B C B' C H2 H3 H6).
	     rewrite (CongruentItself A E D E' D' H5 H4 H10 H8).
	       apply (CongruentOppParallelogramm A C B' E' D').
	      autoClockwise.
	      apply (BetweenHalfLineBetween B' A D D').
	       apply BetweenSym; apply (BetweenHalfLineBetween D A B B').
	        apply BetweenSym; trivial.
	        trivial.
	       trivial.
	      auto.
	      auto.
	      auto.
	      intro; elim H1.
	        apply (CollinearTrans A B' B C).
	       apply (EquiDistantDistinct A C A B' H3); auto.
	       apply CollinearACB; apply HalfLineCollinear; trivial.
	       autoCollinear.
	     autoCollinear.
 Qed.

Lemma CongruentOpposedStrictTriangles : forall A B C D I : Point,
	Between A I C ->
	Between B I D ->
	Distance I A = Distance I C ->
	Distance I B = Distance I D ->
	~Collinear A I B ->
	CongruentStrictTriangles A I B C I D.
Proof.
	intros.
	apply CongruentStrictTrianglesSASB.
	 trivial.
	 trivial.
	 rewrite (AngleSym I A B).
	  apply CongruentOpp.
	   trivial.
	   trivial.
	   intro; elim H3; autoCollinear.
	  apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H).
	  apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H0).
	 trivial.
Qed.

End OPPOSED_ANGLE.

