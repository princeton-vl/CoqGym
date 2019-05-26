Require Export D5_ParalleleConst.

Section SUM_ANGLES_PROPERTIES.

Lemma SumAnglesRec : forall A B C D E : Point,
	Clockwise A B C ->
	Clockwise A C D ->
	Between B A E ->
	Angle B A C = Angle A C D ->
	Angle D A E = Angle A D C.
Proof.
	intros.
	destruct (ExistsCongruentStrictTriangle D A C A D) as (F, (H3, H4)).
	 autoClockwise.
	 autoDistance.
	 rewrite (CongruentStrictTrianglesA _ _ _ _ _ _ H3).
	   apply HalfLineAngleC.
	  autoDistinct.
	  apply (BetweenDistinctBC _ _ _ H1).
	  assert (H5 : Between B A F).
	   apply (SumAngles A B C D F H H0 H4 H2).
	     rewrite (CongruentStrictTrianglesA _ _ _ _ _ _ H3); trivial.
	   assert (H6 := EquiOrientedRev _ _ _ H1); canonize.
Qed.

Lemma SumAnglesCorollary : forall A B C D E A' B' C' : Point,
	Clockwise A' B' C' ->
	Clockwise A B C ->
	Clockwise A C D ->
	Angle B A C = Angle A' B' C' ->
	Angle C A D = Angle B' A' C' ->
	Between B A E ->
	Angle D A E = Angle A' C' B'.
Proof.
	intros.
	destruct (ExistsHalfLineEquidistant A C A' B') as (B'', (H6, H7)).
	 autoDistinct.
	 autoDistinct.
	 destruct (ExistsHalfLineEquidistant A D A' C') as (C'', (H8, H9)).
	  autoDistinct.
	  autoDistinct.
	  assert (H10 : CongruentStrictTriangles A' B' C' A B'' C'').
	   apply CongruentStrictTrianglesSASA.
	    auto.
	    auto.
	    rewrite <- H3; apply HalfLineAngleBC.
	     autoDistinct.
	     autoDistinct.
	     trivial.
	     trivial.
	    exact (ClockwiseNotCollinear _ _ _ H).
	   rewrite (CongruentStrictTrianglesC _ _ _ _ _ _ H10).
	     rewrite (HalfLineAngleB A D E C'').
	    apply (SumAnglesRec A B).
	     apply ClockwiseBCA; generalizeChangeSense.
	       apply H4; autoClockwise.
	     generalizeChangeSense.
	       apply H6; apply ClockwiseBCA; apply H12; autoClockwise.
	     trivial.
	     rewrite <- (CongruentStrictTrianglesB _ _ _ _ _ _ H10); rewrite <- H2.
	       apply HalfLineAngleC.
	      autoDistinct.
	      apply (HalfLineDistinct A C B'').
	       autoDistinct.
	       trivial.
	      apply HalfLineSym.
	       autoDistinct.
	       trivial.
	    autoDistinct.
	    exact (BetweenDistinctBC _ _ _ H4).
	    trivial.
Qed.

Lemma TwoEmbeddedTriangles : forall A B C D E : Point,
	Clockwise A B C ->
	Between A D B ->
	Between A E C ->
	Angle A D E = Angle A B C ->
	Angle A E D = Angle A C B.
Proof.
	intros.
	destruct (ExistsDParallelogramm _ _ _ (ClockwiseBCA _ _ _ H)) as (F, H3).
	destruct
	 (CentralSymetPoint F A (sym_not_eq (ParallelogrammDistinctCD _ _ _ _ H3)))
	 as (G, (_, H4)).
	rewrite <- (SumAnglesRec A F B C G).
	 rewrite <- (SumAnglesRec A F D E G).
	  apply BetweenAngleB.
	   exact (BetweenDistinctBC _ _ _ H4).
	   trivial.
	  apply ClockwiseBCA; apply (BetweenClockwiseMBC B A F D).
	   apply ClockwiseCAB;
	    apply
	     (ParallelogrammClockwiseBCD _ _ _ _ (ParallelogrammPermut _ _ _ _ H3)).
	   exact (BetweenSym _ _ _ H0).
	  exact (TriangleAMN A B C D E H H0 H1).	
	  trivial.
	  rewrite (BetweenAngleC A F D B).
	   rewrite H2; assert (H5 := ParallelogrammCongruentTrianglesAC _ _ _ _ H3).
	     rewrite <- (CongruentStrictTrianglesA _ _ _ _ _ _ H5).
	     apply AngleSym; autoDistinct.
	   apply sym_not_eq; exact (BetweenDistinctAB _ _ _ H4).
	   trivial.
	 apply (ParallelogrammClockwiseBCD _ _ _ _ (ParallelogrammPermut _ _ _ _ H3)).
	 trivial.
	 trivial.
	 assert (H5 := ParallelogrammCongruentTrianglesAC _ _ _ _ H3).
	   rewrite <- (CongruentStrictTrianglesA _ _ _ _ _ _ H5).
	   apply AngleSym; autoDistinct.
Qed.

Lemma TwoEmbeddedSymTriangles : forall A B C D E : Point,
	Clockwise A B C ->
	Between A D B ->
	Between A E C ->
	Angle A E D = Angle A C B ->
	Angle A D E = Angle A B C.
Proof.
	intros.
	destruct (ExistsHalfLineEquidistant A C A B) as (B', (H3, H4)).
	 autoDistinct.
	 autoDistinct.
	 destruct (ExistsHalfLineEquidistant A B A C) as (C', (H5, H6)).
	  autoDistinct.
	  autoDistinct.
	  assert (H7 := TriangleAMN A B C D E H H0 H1).
	    destruct (ExistsHalfLineEquidistant A E A D) as (D', (H8, H9)).
	   autoDistinct.
	   autoDistinct.
	   destruct (ExistsHalfLineEquidistant A D A E) as (E', (H10, H11)).
	    autoDistinct.
	    autoDistinct.
	    assert (H12 : CongruentStrictTriangles A B C A B' C').
	     apply CongruentStrictTrianglesSASA.
	      auto.
	      auto.
	      apply CongruentItself; autoDistinct.
	      exact (ClockwiseNotCollinear _ _ _ H).
	     assert (H13 : CongruentStrictTriangles A D E A D' E').
	      apply CongruentStrictTrianglesSASA.
	       auto.
	       auto.
	       apply CongruentItself; autoDistinct.
	       exact (ClockwiseNotCollinear _ _ _ H7).
	      rewrite (CongruentStrictTrianglesB _ _ _ _ _ _ H12).
	        rewrite (CongruentStrictTrianglesB _ _ _ _ _ _ H13).
	        apply TwoEmbeddedTriangles.
	       generalizeChangeSense.
	         apply H5; apply ClockwiseBCA.
	         apply H1; autoClockwise.
	       apply LSltBetween.
	        apply (HalfLineDistinct A D); [ autoDistinct | auto ].
	        assert (H14 := BetweenHalfLine _ _ _ H0).
	          canonize.
	          apply H5; apply H14.
	          clear H3 H5 H8 H14 H16 H17; generalizeChange.
	        rewrite H11; rewrite H6; exact (BetweenLSlt _ _ _ H1).
	       apply LSltBetween.
	        apply (HalfLineDistinct A E); [ autoDistinct | auto ].
	        assert (H14 := BetweenHalfLine _ _ _ H1).
	          canonize.
	          apply H3; apply H14.
	          clear H3 H5 H10 H14 H16 H17; generalizeChange.
	        rewrite H9; rewrite H4; exact (BetweenLSlt _ _ _ H0).
	       rewrite <- (CongruentStrictTrianglesC _ _ _ _ _ _ H12).
	         rewrite <- (CongruentStrictTrianglesC _ _ _ _ _ _ H13).
	         trivial.
Qed.

Lemma ExternParallelogramm  : forall A B C D E : Point,
	Parallelogramm A B C D ->
	Between D C E ->
	Angle A B C = Angle B C E.
Proof.
	intros.
	rewrite (AngleSym B).
	 apply sym_eq; apply (SumAnglesRec C D A B E).
	  apply (ParallelogrammClockwiseBCD _ _ _ _ (ParallelogrammPermut _ _ _ _ H)).
	  apply (ParallelogrammClockwiseBDA _ _ _ _ (ParallelogrammPermut _ _ _ _ H)).
	  trivial.
	  rewrite (AngleSym A).
	   apply sym_eq; apply CongruentStrictTrianglesA.
	     exact (ParallelogrammCongruentTrianglesAC _ _ _ _ H).
	   exact (ParallelogrammDistinctAC _ _ _ _ H).
	   exact (ParallelogrammDistinctAB _ _ _ _ H).
	 exact (sym_not_eq (ParallelogrammDistinctAB _ _ _ _ H)).
	 exact (ParallelogrammDistinctAB _ _ _ _ (ParallelogrammPermut _ _ _ _ H)).
Qed.

Lemma ExternOppParallelogramm  : forall A B C D E : Point,
	Parallelogramm A B C D ->
	Between B C E ->
	Angle A B C = Angle D C E.
Proof.
	intros.
	destruct (CentralSymetPoint D C) as (F, (H1, H2)).
	 apply sym_not_eq; exact (ParallelogrammDistinctCD _ _ _ _ H).
	 rewrite (ExternParallelogramm _ _ _ _ _ H H2).
	   apply CongruentOpp.
	  trivial.
	  exact (BetweenSym _ _ _ H2).
	  apply ClockwiseNotCollinear.
	    apply ClockwiseBCA; apply (EquiOrientedRev _ _ _ (BetweenSym _ _ _ H2)).
	    canonize; apply ClockwiseBCA;
	     exact (ParallelogrammClockwiseBCD _ _ _ _ H).
Qed.

Lemma ParallelogrammExtern  : forall A B C D E : Point,
	Parallelogramm A B C D ->	
	Clockwise C B E ->
	Angle A B C = Angle B C E ->
	Between D C E.
Proof.
	intros.
	apply (SumAngles C D A B E).
	 exact (ParallelogrammClockwiseBCD _ _ _ _ (ParallelogrammPermut _ _ _ _ H)).
	 exact (ParallelogrammClockwiseBDA _ _ _ _ (ParallelogrammPermut _ _ _ _ H)).
	 trivial.
	 assert (H2 := ParallelogrammCongruentTrianglesAC _ _ _ _ H).
	   apply sym_eq; rewrite (AngleSym A).
	  exact (CongruentStrictTrianglesA _ _ _ _ _ _ H2).
	  exact (ParallelogrammDistinctAC _ _ _ _ H).
	  exact (ParallelogrammDistinctAB _ _ _ _ H).
	 rewrite (AngleSym B); auto.
	  autoDistinct.
	  exact (sym_not_eq (ParallelogrammDistinctAB _ _ _ _ H)).
Qed.

End SUM_ANGLES_PROPERTIES.

