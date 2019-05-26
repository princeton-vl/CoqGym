Require Export C3_Triangles_Egaux.

Section CONGRUENT_STRICT_TRIANGLES.

Definition CongruentStrictTriangles (A B C A' B' C' : Point) :=
	CongruentTriangles A B C A' B' C' /\
	~Collinear A B C.

Lemma CongruentStrictTrianglesSym : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	CongruentStrictTriangles A' B' C' A B C.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	 apply CongruentTrianglesSym; trivial.
	 unfold CongruentTriangles in H0; decompose [and] H0; clear H0.
	   assert (A' <> B').
	  intro; subst.
	    elim (NotCollinearDistinctAB _ _ _ H1).
	    apply DistNull; rewrite H2; apply NullDist.
	  decompose [or] (FourCases A' B' C').
	   elim (CollinearNotClockwiseABC _ _ _ H); trivial.
	   elim (CollinearNotClockwiseBAC _ _ _ H); trivial.
	   decompose [or] (FourCases B' C' A').
	    elim (CollinearNotClockwiseABC _ _ _ H); apply ClockwiseCAB; trivial.
	    elim (CollinearNotClockwiseBAC _ _ _ H); apply ClockwiseBCA; trivial.
	    destruct (ChaslesRec A C B).
	     rewrite (DistSym A C); rewrite H5; rewrite (DistSym C' A').
	       rewrite (DistSym C B); rewrite H4; rewrite (DistSym B' C').
	       rewrite H2; apply Chasles.
	      apply HalfLineSym; trivial.
	      trivial.
	     elim H1; apply CollinearACB; apply HalfLineCollinear; trivial.
	    destruct (ChaslesRec A B C).
	     rewrite H2; rewrite H4; rewrite (DistSym A C); rewrite H5;
	      rewrite (DistSym C' A').
	       apply Chasles; auto.
	     elim H1; apply HalfLineCollinear; trivial.
	   decompose [or] (FourCases A' C' B').
	    elim (CollinearNotClockwiseBAC _ _ _ H); apply ClockwiseCAB; trivial.
	    elim (CollinearNotClockwiseABC _ _ _ H); apply ClockwiseBCA; trivial.
	    destruct (ChaslesRec A C B).
	     rewrite (DistSym A C); rewrite H5; rewrite (DistSym C' A').
	       rewrite (DistSym C B); rewrite H4; rewrite (DistSym B' C').
	       rewrite H2; apply Chasles.
	      trivial.
	      apply HalfLineSym; auto.
	     elim H1; apply CollinearACB; apply HalfLineCollinear; trivial.
	    destruct (ChaslesRec B A C).
	     rewrite (DistSym B A); rewrite H2; rewrite (DistSym A' B').
	       rewrite (DistSym A C); rewrite H5; rewrite (DistSym C' A').
	       rewrite H4; apply Chasles; trivial.
	     elim H1; apply CollinearBAC; apply HalfLineCollinear; trivial.
Qed.

Lemma CongruentStrictTrianglesBAC : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	CongruentStrictTriangles B A C B' A' C'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	 apply CongruentTrianglesBAC; trivial.
	 elim H1; autoCollinear.
Qed.

Lemma CongruentStrictTrianglesACB : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	CongruentStrictTriangles A C B A' C' B'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	 apply CongruentTrianglesACB; trivial.
	 elim H1; autoCollinear.
Qed.

Lemma CongruentStrictTrianglesCBA : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	CongruentStrictTriangles C B A C' B' A'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	 apply CongruentTrianglesCBA; trivial.
	 elim H1; autoCollinear.
Qed.

Lemma CongruentStrictTrianglesBCA : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	CongruentStrictTriangles B C A B' C' A'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	 apply CongruentTrianglesBCA; trivial.
	 elim H1; autoCollinear.
Qed.

Lemma CongruentStrictTrianglesCAB : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	CongruentStrictTriangles C A B C' A' B'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	 apply CongruentTrianglesCAB; trivial.
	 elim H1; autoCollinear.
Qed.

Lemma CongruentStrictTrianglesAB : forall A B C A' B' C' : Point,
        CongruentStrictTriangles A B C A' B' C' ->
        Distance A B = Distance A' B'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply (CongruentTrianglesAB _ _ _ _ _ _ H0).
Qed.

Lemma CongruentStrictTrianglesBC : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	Distance B C = Distance B' C'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply (CongruentTrianglesBC _ _ _ _ _ _ H0).
Qed.

Lemma CongruentStrictTrianglesCA : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	Distance C A = Distance C' A'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply (CongruentTrianglesCA _ _ _ _ _ _ H0).
Qed.

Lemma CongruentStrictTrianglesA : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	Angle B A C = Angle B' A' C'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply CongruentTrianglesA.
	 trivial.
	 apply (NotCollinearDistinctAB _ _ _ H1).
	 apply (sym_not_eq (NotCollinearDistinctCA _ _ _ H1)).
Qed.

Lemma CongruentStrictTrianglesB : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	Angle A B C = Angle A' B' C'.
Proof.
	intros; apply CongruentStrictTrianglesA.
	apply CongruentStrictTrianglesBAC; trivial.
Qed.

Lemma CongruentStrictTrianglesC : forall A B C A' B' C' : Point,
	CongruentStrictTriangles A B C A' B' C' ->
	Angle A C B = Angle A' C' B'.
Proof.
	intros; apply CongruentStrictTrianglesA.
	apply CongruentStrictTrianglesCAB; trivial.
Qed.

Lemma CongruentStrictTrianglesSASA : forall A B C A' B' C' : Point,
	Distance A B = Distance A' B' ->
	Distance A C = Distance  A' C' ->
	Angle B A C = Angle B' A'  C' ->
	~Collinear A B C ->
	CongruentStrictTriangles A B C A' B' C'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply CongruentTrianglesSASA; auto.
	 apply (NotCollinearDistinctAB _ _ _ H2).
	 apply (sym_not_eq (NotCollinearDistinctCA _ _ _ H2)).
Qed.

Lemma CongruentStrictTrianglesSASB : forall A B C A' B' C' : Point,
	Distance B A = Distance B' A' ->
	Distance B C = Distance  B' C' ->
	Angle A B C = Angle A' B' C' ->
	~Collinear A B C ->
	CongruentStrictTriangles A B C A' B' C'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply CongruentTrianglesSASB; auto.
	 apply (sym_not_eq (NotCollinearDistinctAB _ _ _ H2)).
	 apply (NotCollinearDistinctBC _ _ _ H2).
Qed.

Lemma CongruentStrictTrianglesSASC : forall A B C A' B' C' : Point,
	Distance C A = Distance C' A'  ->
	Distance C B = Distance  C' B'  ->
	Angle A C B = Angle A' C' B' ->
	~Collinear A B C ->
	CongruentStrictTriangles A B C A' B' C'.
Proof.
	unfold CongruentStrictTriangles in |- *; intuition.
	apply CongruentTrianglesSASC; auto.
	 apply (NotCollinearDistinctCA _ _ _ H2).
	 apply (sym_not_eq (NotCollinearDistinctBC _ _ _ H2)).
Qed.

Lemma EquiDirectedCollinear : forall A B C : Point,
	EquiDirected A B B C ->
	Collinear A B C.
Proof.
	generalizeChange.
	 elim (NotClockwiseBAA C B); auto.
	 elim (NotClockwiseBAA A B); apply H1; [ autoDistinct | autoClockwise ].
	 elim (NotClockwiseABA C B); auto.
	 assert (H2 := sym_not_eq (ClockwiseDistinctAB _ _ _ H0)).
	   elim (NotClockwiseBAA C B).
	   assert (H3 := H1 H2); clear H1.
	   generalizeChange.
	   apply H6; [ autoDistinct | autoClockwise ].
	 elim (NotClockwiseABA C B); auto.
	 elim (NotClockwiseBAA C B); auto.
	 elim (NotClockwiseABA A B); apply H1; [ autoDistinct | autoClockwise ].
	 elim (NotClockwiseABA C B); auto.
	 elim (NotClockwiseABA A B); apply H0; autoClockwise.
	 elim (NotClockwiseABA C B); apply H1; [ autoDistinct | autoClockwise ].
	 elim (NotClockwiseBAA A B); apply H; autoClockwise.
	 elim (NotClockwiseABA A B); apply H2; autoClockwise.
	 assert (H2 := sym_not_eq (ClockwiseDistinctBC _ _ _ H)).
	   assert (H3 := H1 H2); clear H1.
	   generalizeChange.
	   elim (NotClockwiseABA C B); auto.
	 elim (NotClockwiseBAA C B); apply H1; [ autoDistinct | autoClockwise ].
	 elim (NotClockwiseBAA C B); apply H1; [ autoDistinct | autoClockwise ].
	 elim (NotClockwiseBAA A B); apply H0; autoClockwise.
Qed.

Lemma ClockwiseEq : forall A B C D : Point,
	Clockwise A B C ->
	Collinear A B D ->
	Collinear B C D ->
	B = D.
Proof.
	intros.
	assert (H2 := ClockwiseDistinctAB _ _ _ H).
	assert (H3 := ClockwiseDistinctBC _ _ _ H).
	setLine A B H2 ipattern:(AB) ipattern:(D1).
	setLine B C H3 ipattern:(BC) ipattern:(D2).
	setLinterL AB BC D1 D2 ipattern:(E) ipattern:(H4) ipattern:(H5) ipattern:(H6).
	 intro H4; elim (ClockwiseNotCollinear _ _ _ H).
	   apply EquiDirectedCollinear; trivial.
	 rewrite <- (H6 D); intuition.
	   apply sym_eq; apply (H6 B); split; autoCollinear.
Qed.

Lemma CongruentStrictTrianglesASAAB : forall A B C A' B' C' : Point,
	Distance A B = Distance A' B' ->
	Angle B A C = Angle B' A'  C' ->
	Angle A B C = Angle A' B' C' ->
	~Collinear A B C ->
	CongruentStrictTriangles A B C A' B' C'.
Proof.
	intros.
	decompose [or] (FourCases A' B' C').
	 destruct (ExistsHalfLineEquidistant A' C' A C) as (C'', (H4, H5)).
	  autoDistinct.
	  assert (H4 := NotCollinearDistinctCA _ _ _ H2); auto.
	  assert (H6 : CongruentStrictTriangles A B C A' B' C'').
	   apply CongruentStrictTrianglesSASA; auto.
	     rewrite H0; apply (HalfLineAngleC A' B' C' C''); autoDistinct.
	   assert (H7 : C' = C'').
	    apply (ClockwiseEq B' C' A' C'').
	     autoClockwise.
	     apply HalfLineCollinear.
	       apply (AngleBHalfLine B' C' A' C'').
	      autoClockwise.
	      generalizeChangeSense.
	        apply ClockwiseCAB; apply H2; autoClockwise.
	      rewrite AngleSym; [ rewrite <- H1 | autoDistinct | autoDistinct ].
	        rewrite (AngleSym B' C'' A').
	       apply (CongruentStrictTrianglesB _ _ _ _ _ _ H6).
	       intro; subst.
	         elim (ClockwiseNotCollinear _ _ _ H3); apply CollinearACB;
	          apply HalfLineCollinear; trivial.
	       autoDistinct.
	     apply CollinearBAC; apply HalfLineCollinear; trivial.
	    rewrite H7; trivial.
	 destruct (ExistsHalfLineEquidistant B' C' B C) as (C'', (H5, H6)).
	  autoDistinct.
	  apply (NotCollinearDistinctBC _ _ _ H2); trivial.
	  assert (H7 : CongruentStrictTriangles B A C B' A' C'').
	   apply CongruentStrictTrianglesSASA.
	    autoDistance.
	    autoDistance.
	    rewrite H1; apply (HalfLineAngleC B' A' C' C''); autoDistinct.
	    intro; elim H2; autoCollinear.
	   assert (H8 : C' = C'').
	    apply (ClockwiseEq A' C' B' C'').
	     autoClockwise.
	     apply HalfLineCollinear.
	       apply (AngleBHalfLine A' C' B' C'').
	      autoClockwise.
	      generalizeChangeSense.
	        apply ClockwiseCAB; apply H2; autoClockwise.
	      rewrite AngleSym; [ rewrite <- H0 | autoDistinct | autoDistinct ].
	        rewrite (AngleSym A' C'' B').
	       apply (CongruentStrictTrianglesB _ _ _ _ _ _ H7).
	       intro; subst.
	         elim (ClockwiseNotCollinear _ _ _ H4); apply CollinearACB;
	          apply HalfLineCollinear; trivial.
	       autoDistinct.
	     apply CollinearBAC; apply HalfLineCollinear; trivial.
	    rewrite H8; apply CongruentStrictTrianglesBAC; trivial.
	 elim H2; assert (A' <> B').
	  intro; subst.
	    elim (NotCollinearDistinctAB _ _ _ H2).
	    apply DistNull; rewrite H; apply NullDist.
	  rewrite (NullAngle A' B' C' H4 H3) in H0.
	    apply HalfLineCollinear; apply NullAngleHalfLine.
	   apply (NotCollinearDistinctAB _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctCA _ _ _ H2)).
	   trivial.
	 elim H2; assert (B' <> A').
	  intro; subst.
	    elim (NotCollinearDistinctAB _ _ _ H2).
	    apply DistNull; rewrite H; apply NullDist.
	  rewrite (NullAngle B' A' C' H4 H3) in H1.
	    apply CollinearBAC; apply HalfLineCollinear; apply NullAngleHalfLine.
	   apply (sym_not_eq (NotCollinearDistinctAB _ _ _ H2)).
	   apply (NotCollinearDistinctBC _ _ _ H2).
	   trivial.
Qed.

Lemma CongruentStrictTrianglesASABC : forall A B C A' B' C' : Point,
	Distance B C = Distance B' C' ->
	Angle A B C = Angle A' B' C' ->
	Angle B C A = Angle B'  C' A' ->
	~Collinear A B C ->
	CongruentStrictTriangles A B C A' B' C'.
Proof.
	intros; apply CongruentStrictTrianglesCAB.
	decompose [or] (FourCases B' C' A').
	 apply CongruentStrictTrianglesASAAB.
	  trivial.
	  rewrite AngleSym.
	   rewrite H0; apply AngleSym; autoDistinct.
	   apply (NotCollinearDistinctBC _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctAB _ _ _ H2)).
	  trivial.
	  intro; elim H2; autoCollinear.
	 apply CongruentStrictTrianglesASAAB.
	  trivial.
	  rewrite AngleSym.
	   rewrite H0; apply AngleSym; autoDistinct.
	   apply (NotCollinearDistinctBC _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctAB _ _ _ H2)).
	  trivial.
	  intro; elim H2; autoCollinear.
	 elim H2; assert (B' <> C').
	  intro; subst.
	    elim (NotCollinearDistinctBC _ _ _ H2).
	    apply DistNull; rewrite H; apply NullDist.
	  assert (H5 := NullAngle B' C' A' H4 H3).
	    apply CollinearBAC; apply HalfLineCollinear; apply NullAngleHalfLine.
	   apply (sym_not_eq (NotCollinearDistinctAB _ _ _ H2)).
	   apply (NotCollinearDistinctBC _ _ _ H2).
	   rewrite H0; rewrite <- H5.
	     apply AngleSym.
	    apply (HalfLineDistinct B' C' A' H4 H3).
	    trivial.
	 elim H2; assert (C' <> B').
	  intro; subst.
	    elim (NotCollinearDistinctBC _ _ _ H2).
	    apply DistNull; rewrite H; apply NullDist.
	  apply CollinearCBA; apply HalfLineCollinear; apply NullAngleHalfLine.
	   apply (sym_not_eq (NotCollinearDistinctBC _ _ _ H2)).
	   apply (NotCollinearDistinctCA _ _ _ H2).
	   rewrite H1; apply NullAngle; trivial.
Qed.

Lemma CongruentStrictTrianglesASACA : forall A B C A' B' C' : Point,
	Distance C A = Distance C' A' ->
	Angle B C A = Angle B' C'  A' ->
	Angle B A C = Angle B' A' C' ->
	~Collinear A B C ->
	CongruentStrictTriangles A B C A' B' C'.
Proof.
	intros; apply CongruentStrictTrianglesBCA.
	decompose [or] (FourCases C' A' B').
	 apply CongruentStrictTrianglesASAAB.
	  trivial.
	  rewrite AngleSym.
	   rewrite H0; apply AngleSym.
	    autoDistinct.
	    autoDistinct.
	   apply (NotCollinearDistinctCA _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctBC _ _ _ H2)).
	  rewrite AngleSym.
	   rewrite H1; apply AngleSym; autoDistinct.
	   apply (sym_not_eq (NotCollinearDistinctCA _ _ _ H2)).
	   apply (NotCollinearDistinctAB _ _ _ H2).
	  intro; elim H2; autoCollinear.
	 apply CongruentStrictTrianglesASAAB.
	  trivial.
	  rewrite AngleSym.
	   rewrite H0; apply AngleSym; autoDistinct.
	   apply (NotCollinearDistinctCA _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctBC _ _ _ H2)).
	  rewrite AngleSym.
	   rewrite H1; apply AngleSym; autoDistinct.
	   apply (sym_not_eq (NotCollinearDistinctCA _ _ _ H2)).
	   apply (NotCollinearDistinctAB _ _ _ H2).
	  intro; elim H2; autoCollinear.
	 elim H2; assert (C' <> A').
	  intro; subst.
	    elim (NotCollinearDistinctCA _ _ _ H2).
	    apply DistNull; rewrite H; apply NullDist.
	  apply CollinearBCA; apply HalfLineCollinear; apply NullAngleHalfLine.
	   apply (NotCollinearDistinctCA _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctBC _ _ _ H2)).
	   rewrite AngleSym.
	    rewrite H0; apply NullAngle.
	     apply (HalfLineDistinct C' A' B' H4 H3).
	     apply HalfLineSym; trivial.
	    apply (NotCollinearDistinctCA _ _ _ H2).
	    apply (sym_not_eq (NotCollinearDistinctBC _ _ _ H2)).
	 elim H2; assert (A' <> C').
	  intro; subst.
	    elim (NotCollinearDistinctCA _ _ _ H2).
	    apply DistNull; rewrite H; apply NullDist.
	  apply HalfLineCollinear; apply NullAngleHalfLine.
	   apply (NotCollinearDistinctAB _ _ _ H2).
	   apply (sym_not_eq (NotCollinearDistinctCA _ _ _ H2)).
	   rewrite H1; apply NullAngle.
	    apply (HalfLineDistinct A' C' B' H4 H3).
	    apply HalfLineSym; trivial.
Qed.

End CONGRUENT_STRICT_TRIANGLES.
