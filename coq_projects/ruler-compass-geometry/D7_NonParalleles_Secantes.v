Require Export D6_SumAnglesProp.

Require Export Omega.

Section DISTINCT_PARALLEL.

Lemma ThreeEmbeddedTriangles : forall A B C D E F G : Point,
	Clockwise A B C ->
	HalfLine A B D ->
	HalfLine A C E ->
	Angle A B C = Angle A D E ->
	Angle A C B = Angle A E D ->
	Between A D F ->
	Between A E G ->
	Distance D F = Distance A B ->
	Distance E G = Distance A C ->
	Angle A B C = Angle A F G /\ Angle A C B = Angle A G F.
Proof.
	intros.
	assert (H8 : Clockwise E D F).
	 generalizeChangeSense.
	   apply ClockwiseCAB; apply H9; apply H0.
	   apply ClockwiseBCA; apply H11; autoClockwise.
	 destruct (ExistsDParallelogramm _ _ _ H8) as (I, H9).
	   assert (CongruentStrictTriangles A B C E I G).
	  apply CongruentStrictTrianglesSASA.
	   assert (H10 := ParallelogrammCongruentTrianglesAC _ _ _ _ (ParallelogrammPermut _ _ _ _ H9)).
	     rewrite (DistSym E I); rewrite <- (CongruentStrictTrianglesAB _ _ _ _ _ _ H10); auto.
	   auto.
	   apply sym_eq; apply (SumAnglesCorollary E A D I G B C A).
	    autoClockwise.
	    generalizeChangeSense.
	      apply H13; apply ClockwiseCAB; apply H0; autoClockwise.
	    apply ClockwiseCAB; exact (ParallelogrammClockwiseBDA _ _ _ _ H9).
	    rewrite <- H3; apply AngleSym.
	     autoDistinct.
	     autoDistinct.
	    rewrite (AngleSym E).
	     rewrite (ExternParallelogramm I E D F A).
	      rewrite (AngleSym D).
	       rewrite (AngleSym B); auto; autoDistinct.
	       autoDistinct.
	       exact (sym_not_eq (BetweenDistinctAB _ _ _ H4)).
	      do 3 apply ParallelogrammPermut; trivial.
	      exact (BetweenSym _ _ _ H4).
	     autoDistinct.
	     exact (sym_not_eq (ParallelogrammDistinctCD _ _ _ _ (ParallelogrammPermut _ _ _ _ H9))).
	    trivial.
	   exact (ClockwiseNotCollinear _ _ _ H).
	  assert (H11 : Between F I G).
	   apply (SupplementaryRec I F E G).
	    apply (ParallelogrammClockwiseBCD _ _ _ _ (ParallelogrammPermut _ _ _ _ H9)).
	    apply ClockwiseBCA; apply (EquiOrientedRev _ _ _ (BetweenSym _ _ _ H5)).
	      canonize; apply ClockwiseBCA.
	      apply (HalfLineParallel I E D F A).
	     do 3 apply ParallelogrammPermut; trivial.
	     apply BetweenSymHalfLine; canonize.
	    rewrite <- (CongruentStrictTrianglesB _ _ _ _ _ _ H10); rewrite H2.
	      rewrite <- (CongruentStrictTrianglesB _ _ _ _ _ _ (ParallelogrammCongruentTrianglesAC _ _ _ _ H9)).
	      apply SupplementaryCommut; exists D; exists A; exists E; exists F; intuition.
	      autoDistinct.
	   split.
	    rewrite (HalfLineAngleBC F A G D I).
	     rewrite (ExternOppParallelogramm D F I E G).
	      exact (CongruentStrictTrianglesB _ _ _ _ _ _ H10).
	      exact (ParallelogrammPermut _ _ _ _ H9).
	      trivial.
	     exact (BetweenDistinctCA _ _ _ H4).
	     apply sym_not_eq; exact (BetweenDistinctCA _ _ _ H11).
	     apply HalfLineSym.
	      autoDistinct.
	      exact (BetweenSymHalfLine _ _ _ H4).
	     apply HalfLineSym.
	      exact (BetweenDistinctAB _ _ _ H11).
	      exact (BetweenHalfLine _ _ _ H11).
	    rewrite (HalfLineAngleBC G A F E I).
	     exact (CongruentStrictTrianglesC _ _ _ _ _ _ H10).
	     exact (BetweenDistinctCA _ _ _ H5).
	     exact (BetweenDistinctCA _ _ _ H11).
	     apply HalfLineSym.
	      apply sym_not_eq; exact (BetweenDistinctBC _ _ _ H5).
	      exact (BetweenSymHalfLine _ _ _ H5).
	     apply HalfLineSym.
	      apply sym_not_eq; exact (BetweenDistinctBC _ _ _ H11).
	      exact (BetweenSymHalfLine _ _ _ H11).
Qed.

Lemma EmbeddedSimilarTriangles : forall A B C : Point, forall n : nat,
	Clockwise A B C ->
	n > 0 ->
	forall D E : Point,
		HalfLine A B D ->
		HalfLine A C E ->
		Distance A D = DistTimesn n A B ->
		Distance A E = DistTimesn n A C ->
		Angle A B C = Angle A D E /\ Angle A C B = Angle A E D.
Proof.
	intros A B C n H Hn.
	assert (Hab := ClockwiseDistinctAB _ _ _ H).
	assert (Hac := sym_not_eq (ClockwiseDistinctCA _ _ _ H)).
	induction Hn.
	 simpl in |- *; rewrite NullDist; do 2 rewrite LS0NeutralRight; intros.
	   rewrite (HalfLineEquidistantEqual A B D Hab H0 (sym_eq H2)).
	   rewrite (HalfLineEquidistantEqual A C E Hac H1 (sym_eq H3)).
	   auto.
	 destruct (StrongGraduation A B Hab m) as (Dm, (H0, (H1, H2))).
	   destruct (StrongGraduation A C Hac m) as (Em, (H3, (H4, H5))).
	   assert (A <> Dm).
	  apply H2; omega.
	  assert (A <> Em).
	   apply H5; omega.
	   destruct
	    (IHHn Dm Em (HalfLineSym _ _ _ H6 H0) (HalfLineSym _ _ _ H7 H3) H1 H4).
	     clear IHHn H2 H5; simpl in |- *; intros.
	     destruct (ExistsEquidistantBetween A Dm A B H6 Hab) as (DSm, (H12, H13)).
	     assert
	      (H14 :=
	       HalfLineEquidistantEqualPoints _ _ _ _ _ _ H0 H1 H2 H6 H10 H12 H13);
	      subst.
	     subst.
	     destruct (ExistsEquidistantBetween A Em A C H7 Hac) as (ESm, (H14, H15)).
	     assert
	      (H16 :=
	       HalfLineEquidistantEqualPoints _ _ _ _ _ _ H3 H4 H5 H7 H11 H14 H15);
	      subst.
	     apply (ThreeEmbeddedTriangles A B C Dm Em D E); auto.
	    apply (HalfLineSym _ _ _ H6 H0).
	    apply (HalfLineSym _ _ _ H7 H3).
Qed.
	
Lemma ExistsClockwiseParallelogramm : forall A B C D E : Point,
	Parallelogramm A B C D ->
	Between D E A ->
	exists F : Point, Collinear C E F /\ Clockwise B A F.
Proof.
	intros.
	destruct (ExistsDParallelogramm C D E) as (G, H1).
	 apply ClockwiseCAB; apply (BetweenClockwiseAMC D A C E).
	  unfold Parallelogramm in *; intuition; autoClockwise.
	  trivial.
	 assert (H2 := ParallelogrammClockwiseBCD _ _ _ _ H1).
	   destruct (PaschABC D A C E G) as [(I, (H3, H4))| (I, (H3, H4))].
	  unfold Parallelogramm in *; intuition; autoClockwise.
	  trivial.
	  apply ClockwiseNotCollinear; exact H2.
	  intro; elim (ClockwiseNotCollinear E A G).
	   canonize.
	   autoCollinear.
	  unfold Parallelogramm in *; intuition; autoClockwise.
	  elim (BetweenNotClockwiseABC D I C H4).
	    apply ClockwiseBCA; destruct (CollinearHalfLine _ _ _ H3).
	   apply (ParallelHalfLine _ _ _ _ _ H1 H5).
	   apply (HalfLineParallel _ _ _ _ _ H1 H5).
	  assert (H5 := sym_not_eq (BetweenDistinctBC _ _ _ H4)).
	    destruct (Archimedian C I A H5) as (n, H6).
	    assert (H7 : n > 0).
	   destruct n.
	    simpl in H6.
	      elim (AntisymLSlt C A C (BetweenDistinctCA _ _ _ H4) H6).
	      rewrite NullDist; apply (NullLSlt C A (BetweenDistinctCA _ _ _ H4)).
	    auto with arith.
	   destruct (StrongGraduation C I H5 n) as (J, (H8, (H9, H10))).
	     destruct (StrongGraduation C E (ParallelogrammDistinctAC _ _ _ _ H1) n)
	      as (F, (H11, (H12, H13))).
	     assert (H14 : Between C A J).
	    apply LSltBetween.
	     apply (BetweenDistinctCA _ _ _ H4).
	     assert (H14 := BetweenSymHalfLine _ _ _ H4);
	      apply (HalfLineSym C J A (H10 H7)).
	       canonize.
	     rewrite H9; trivial.
	    exists F; split.
	     apply CollinearACB; apply (HalfLineCollinear _ _ _ H11).
	     destruct (ExistsDParallelogramm B A J) as (K, H15).
	      canonize.
	        apply ClockwiseCAB; apply H19.
	        unfold Parallelogramm in *; intuition; autoClockwise.
	      apply (HalfLineParallel _ _ _ _ F H15).
	        apply BetweenSymHalfLine; apply (SupplementaryRec J F C K).
	       apply ClockwiseCAB; apply (ClockwiseBetweenMBC J C F A).
	        apply BetweenSym; trivial.
	        apply ClockwiseCAB; apply (HalfLineSym C F E (H13 H7) H11).
	          canonize; apply ClockwiseCAB; apply (BetweenClockwiseMBC D A C E).
	         apply ClockwiseBCA;
	          apply
	           (ParallelogrammClockwiseBCD B C D A
	              (ParallelogrammPermut _ _ _ _ H)).
	         canonize.
	       apply (ClockwiseBetweenMBC C J K A H14).
	         apply (ParallelogrammClockwiseBCD _ _ _ _ H15).
	      assert (H16 : Clockwise C E I).
	        apply ClockwiseBCA; apply (BetweenClockwiseMBC A C E I).
	         apply ClockwiseBCA; apply (BetweenClockwiseMBC D A C E).
	          apply ClockwiseBCA; apply (ParallelogrammClockwiseBCD B C D A).
	            exact (ParallelogrammPermut _ _ _ _ H).
	          trivial.
	         trivial.
	        destruct
	         (EmbeddedSimilarTriangles C E I n H16 H7 F J
	            (HalfLineSym _ _ _ (H13 H7) H11) (HalfLineSym _ _ _ (H10 H7) H8)
	            H12 H9).
	          rewrite (AngleSym J F C).
	         rewrite <- H18.
	           rewrite <- (BetweenAngleB J A K C).
	          assert
	           (H19 :=
	            ParallelogrammCongruentTrianglesAC _ _ _ _
	              (ParallelogrammPermut _ _ _ _ H15)).
	            rewrite (CongruentStrictTrianglesB _ _ _ _ _ _ H19).
	            rewrite (ExternParallelogramm K B A J C).
	           rewrite
	            (CongruentStrictTrianglesA _ _ _ _ _ _
	               (ParallelogrammCongruentTrianglesAC _ _ _ _ H))
	            .
	             rewrite (AngleSym C).
	            rewrite <- (TwoEmbeddedSymTriangles A C D I E).
	             unfold Supplementary in |- *; exists I; exists C; exists E;
	              exists A; intuition.
	              autoDistinct.
	              exact (BetweenSym _ _ _ H4).
	              apply AngleSym; autoDistinct.
	             apply ClockwiseCAB;
	              exact
	               (ParallelogrammClockwiseBCD _ _ _ _
	                  (ParallelogrammPermut _ _ _ _ H)).
	             trivial.
	             exact (BetweenSym _ _ _ H0).
	             apply sym_eq; rewrite (CongruentItself D A C E C).
	              rewrite (ExternOppParallelogramm _ _ _ _ _ H1 H0).
	                apply CongruentItself.
	               exact (ParallelogrammDistinctCD _ _ _ _ H1).
	               exact (BetweenDistinctBC _ _ _ H0).
	               destruct (ExclusiveCollinear E G I).
	                exact (ParallelogrammDistinctCD _ _ _ _ H1).
	                autoDistinct.
	                trivial.
	                trivial.
	                assert (H21 := EquiOrientedRev _ _ _ H20).
	                  clear H0 H2 H3 H4 H8 H11 H14 H20; generalizeChangeSide.
	                  elim
	                   (ClockwiseNotClockwise _ _ _
	                      (ParallelogrammClockwiseBCD _ _ _ _
	                         (ParallelogrammPermut _ _ _ _ H1))).
	                  apply H4.
	                 exact (ParallelogrammDistinctCD _ _ _ _ H1).
	                 autoClockwise.
	               canonize.
	              apply sym_not_eq; exact (BetweenDistinctCA _ _ _ H0).
	              apply sym_not_eq; exact (ParallelogrammDistinctAB _ _ _ _ H1).
	              apply HalfLineSym.
	               autoClockwise.
	               exact (BetweenHalfLine _ _ _ H0).
	              canonize.
	            exact (ParallelogrammDistinctCD _ _ _ _ H).
	            exact (BetweenDistinctAB _ _ _ H14).
	           do 3 apply ParallelogrammPermut; exact H15.
	           exact (BetweenSym _ _ _ H14).
	          exact (ParallelogrammDistinctCD _ _ _ _ H15).
	          exact (BetweenSym _ _ _ H14).
	         assert (H19 : Clockwise C F J).
	          clear H0 H3 H4 H14; generalizeChange.
	            apply H11; apply ClockwiseBCA.
	            apply H21; autoClockwise.
	          autoDistinct.
	         apply sym_not_eq; auto.
Qed.

Lemma ExistsClockwiseParallelogrammSym : forall A B C D E : Point,
	Parallelogramm A B C D ->
	Between A E C ->
	exists F : Point, Collinear D E F /\ Clockwise B A F.
Proof.
	intros.
	assert (Hacd : Clockwise A C D).
	 unfold Parallelogramm in *; intuition.
	 destruct (ExistsDParallelogramm E C D) as (G, H1).
	  exact (BetweenClockwiseMBC A C D E Hacd H0).
	  assert (Hcge : Clockwise C G E).
	   exact (ParallelogrammClockwiseBDA _ _ _ _ H1).
	   assert (Hedg : Clockwise E D G).
	    unfold Parallelogramm in *; intuition.
	    destruct (PaschABC A C D E G Hacd H0) as [(I, (H3, H4))| (I, (H3, H4))].
	     apply ClockwiseNotCollinear; assert (H2 := EquiOrientedRev _ _ _ H0);
	      canonize.
	       apply H2; autoClockwise.
	     intro; elim (ClockwiseNotCollinear _ _ _ Hcge); autoCollinear.
	     intro; elim (ClockwiseNotCollinear _ _ _ Hedg); autoCollinear.
	     assert (Hdie : Clockwise D I E).
	      apply (BetweenClockwiseAMC D A E I).
	       apply ClockwiseCAB; apply (BetweenClockwiseAMC A C D E Hacd H0).
	       exact (BetweenSym _ _ _ H4).
	      assert (H5 := sym_not_eq (BetweenDistinctBC _ _ _ H4)).
	        destruct (Archimedian D I A H5) as (n, H6).
	        assert (H7 : n > 0).
	       destruct n.
	        simpl in H6.
	          elim (AntisymLSlt D A D (BetweenDistinctCA _ _ _ H4) H6).
	          rewrite NullDist; apply (NullLSlt D A (BetweenDistinctCA _ _ _ H4)).
	        auto with arith.
	       destruct (StrongGraduation D I H5 n) as (J, (H8, (H9, H10))).
	         destruct
	          (StrongGraduation D E
	             (sym_not_eq (ParallelogrammDistinctAC _ _ _ _ H1)) n)
	          as (F, (H11, (H12, H13))).
	         assert (H14 : Between D A J).
	        apply LSltBetween.
	         apply (BetweenDistinctCA _ _ _ H4).
	         assert (H14 := BetweenSymHalfLine _ _ _ H4);
	          apply (HalfLineSym D J A (H10 H7)).
	           canonize.
	         rewrite H9; trivial.
	        exists F; split.
	         apply CollinearACB; apply (HalfLineCollinear _ _ _ H11).
	         destruct (ExistsDParallelogramm B A J) as (K, H15).
	          canonize.
	            apply ClockwiseCAB; apply H18.
	            apply (ParallelogrammClockwiseBCD C D A B);
	             do 2 apply ParallelogrammPermut; trivial.
	          apply (ParallelHalfLine _ _ _ _ F H15).
	            apply (AngleBHalfLine J K D F).
	           apply ClockwiseBCA; apply (ClockwiseBetweenMBC D J K A H14).
	             exact (ParallelogrammClockwiseBCD _ _ _ _ H15).
	           clear H0 H3 H4 H14; generalizeChange.
	             apply ClockwiseCAB; apply H3.
	             apply ClockwiseCAB; apply (H13 E Hdie).
	           assert (H16 : Angle K J D = Angle B A D).
	            rewrite (CongruentItself J K D K A).
	             rewrite (CongruentStrictTrianglesB A J K K B A).
	              apply (ExternParallelogramm K B A J D).
	               do 3 apply ParallelogrammPermut; exact H15.
	               exact (BetweenSym _ _ _ H14).
	              apply ParallelogrammCongruentTrianglesAC.
	                exact (ParallelogrammPermut _ _ _ _ H15).
	             exact (ParallelogrammDistinctCD _ _ _ _ H15).
	             exact (BetweenDistinctCA _ _ _ H14).
	             canonize.
	             apply HalfLineSym.
	              exact (sym_not_eq (BetweenDistinctBC _ _ _ H14)).
	              exact (BetweenSymHalfLine _ _ _ H14).
	            rewrite H16.
	              rewrite (Supplement A J B D I A E D).
	             rewrite (AngleSym I).
	              rewrite (AngleSym J).
	               destruct (EmbeddedSimilarTriangles D I E n Hdie H7 J F).
	                exact (HalfLineSym _ _ _ (H10 H7) H8).
	                exact (HalfLineSym _ _ _ (H13 H7) H11).
	                trivial.
	                trivial.
	                trivial.
	               apply (ClockwiseDistinctBC D J F).
	                 clear H0 H3 H4 H14; generalizeChange.
	                 apply ClockwiseBCA; apply H3.
	                 apply ClockwiseCAB; apply (H13 E Hdie).
	               exact (BetweenDistinctCA _ _ _ H14).
	              autoDistinct.
	              autoDistinct.
	             exact (ParallelogrammDistinctAB _ _ _ _ H).
	             autoDistinct.
	             exact (BetweenSym _ _ _ H14).
	             trivial.
	             rewrite (AngleSym A).
	              rewrite <- (ExternOppParallelogramm C D A B J).
	               rewrite (AngleSym D).
	                apply sym_eq; apply TwoEmbeddedTriangles.
	                 trivial.
	                 trivial.
	                 trivial.
	                 assert (H17 := ParallelogrammPermut _ _ _ _ H1).
	                   rewrite <- (BetweenAngleB C E D A).
	                  rewrite
	                   (CongruentStrictTrianglesB _ _ _ _ _ _
	                      (ParallelogrammCongruentTrianglesAC _ _ _ _ H1))
	                   .
	                    rewrite (ExternParallelogramm D G E C A).
	                   apply CongruentItself.
	                    apply sym_not_eq; exact (BetweenDistinctAB _ _ _ H0).
	                    autoDistinct.
	                    canonize.
	                    destruct (ExclusiveCollinear E I G).
	                     autoDistinct.
	                     autoDistinct.
	                     autoCollinear.
	                     trivial.
	                     elim (ClockwiseNotClockwise G E D).
	                      autoClockwise.
	                      assert (H18 := BetweenSym _ _ _ H2); canonize.
	                        apply H25; autoClockwise.
	                   apply ParallelogrammPermut; trivial.
	                   exact (BetweenSym _ _ _ H0).
	                  autoDistinct.
	                  exact (BetweenSym _ _ _ H0).
	                autoDistinct.
	                autoDistinct.
	               do 2 apply ParallelogrammPermut; trivial.
	               trivial.
	              exact (BetweenDistinctBC _ _ _ H14).
	              exact (ParallelogrammDistinctAB _ _ _ _ H).
	     elim (BetweenNotClockwiseABC _ _ _ (BetweenSym _ _ _ H4)).
	       apply ClockwiseBCA; destruct (CollinearHalfLine _ _ _ H3).
	      apply (HalfLineParallel C D G E I).
	       apply ParallelogrammPermut; trivial.
	       trivial.
	      apply (ParallelHalfLine C D G E I).
	       apply ParallelogrammPermut; trivial.
	       trivial.
Qed.

Lemma SecantParallelogrammSecant : forall A B : Point, forall F F' : Figure, forall D : Line F, forall D' : Line F',
	Parallelogramm (LineA F D) (LineB F D) A B ->
	F' A ->
	~F' B ->
	SecantLines F F' D D'.
Proof.
	intros; destruct (InOrOutLine (LineA F D) F' D').
	 apply (TwoPointsSecantLines A (LineA F D)).
	  unfold Parallelogramm in *; intuition.
	  apply NotClockwiseABA.
	  trivial.
	  trivial.
	 destruct
	  (CentralSymetPoint B A (sym_not_eq (ParallelogrammDistinctCD _ _ _ _ H)))
	  as (C, (H3, H4)).
	   destruct (Apart (LineA F' D') (LineB F' D') A (LineH F' D')).
	  destruct (PaschABC C B (LineA F D) A (LineA F' D'))
	   as [(E, (H6, H7))| (E, (H6, H7))].
	   apply (ClockwiseBetweenMBC C B (LineA F D) A).
	    apply BetweenSym; trivial.
	    apply ClockwiseBCA; unfold Parallelogramm in *; intuition.
	   apply BetweenSym; trivial.
	   intro; elim H1; apply (InFLine F' D').
		     apply (CollinearTrans (LineA F' D') A (LineB F' D') B H5).
	    apply CollinearACB; apply FLineIn; trivial.
	    apply CollinearCAB;
	     apply (CollinearTrans A C B (LineA F' D') (BetweenDistinctBC _ _ _ H4)).
	     apply CollinearBCA; apply BetweenCollinear; trivial.
	     autoCollinear.
	   intro; elim H1; apply (InFLine F' D').
	     apply (CollinearTrans (LineA F' D') A (LineB F' D') B H5).
	    apply CollinearACB; apply FLineIn; trivial.
	    autoCollinear.
	   intro; elim H2; apply (InFLine F' D').
	     apply (CollinearTrans (LineA F' D') A (LineB F' D') (LineA F D) H5).
	    apply CollinearACB; apply FLineIn; trivial.
	    autoCollinear.
	   destruct (ExistsClockwiseParallelogrammSym (LineA F D) (LineB F D) C A E)
	    as (G, (H8, H9)).
	    apply (ParallelogrammSym (LineA F D) (LineB F D) A B C H H3 H4).
	    apply BetweenSym; trivial.
	    apply (TwoPointsSecantLines A G).
	     unfold Parallelogramm in *; intuition.
	     apply ClockwiseNotClockwise; trivial.
	     trivial.
	     apply (InFLine F' D').
	       apply (CollinearTrans (LineA F' D') A (LineB F' D') G H5).
	      apply CollinearACB; apply FLineIn; trivial.
	      apply CollinearBAC; apply (CollinearTrans A E).
	       intro; subst; elim (CollinearNotClockwiseABC (LineA F D) C E).
	        apply CollinearCAB; apply BetweenCollinear; trivial.
	        assert (H10 := EquiOrientedRev _ _ _ (BetweenSym _ _ _ H4)).
	          apply ClockwiseCAB; unfold Parallelogramm in *; intuition; canonize.
	          apply H10; autoClockwise.
	       autoCollinear.
	       trivial.
	   destruct (ExistsClockwiseParallelogramm _ _ _ _ E H H7) as (G, (H8, H9)).
	     apply (TwoPointsSecantLines A G).
	    unfold Parallelogramm in *; intuition.
	    apply ClockwiseNotClockwise; trivial.
	    trivial.
	    apply (InFLine F' D').
	      apply (CollinearTrans (LineA F' D') A (LineB F' D') G H5).
	     apply CollinearACB; apply FLineIn; trivial.
	     apply CollinearBAC; apply (CollinearTrans A E).
	      intro; subst; elim (CollinearNotClockwiseABC (LineA F D) E B).
	       apply CollinearCBA; apply BetweenCollinear; trivial.
	       unfold Parallelogramm in *; intuition.
	      autoCollinear.
	      trivial.
	  destruct (PaschABC C B (LineA F D) A (LineB F' D'))
	   as [(E, (H6, H7))| (E, (H6, H7))].
	   apply (ClockwiseBetweenMBC C B (LineA F D) A).
	    apply BetweenSym; trivial.
	    apply ClockwiseBCA; unfold Parallelogramm in *; intuition.
	   apply BetweenSym; trivial.
	   intro; elim H1; apply (InFLine F' D').
	     apply CollinearBAC;
	      apply (CollinearTrans (LineB F' D') A (LineA F' D') B H5).
	    apply CollinearBCA; apply FLineIn; trivial.
	    apply CollinearCAB;
	     apply (CollinearTrans A C B (LineB F' D') (BetweenDistinctBC _ _ _ H4)).
	     apply CollinearBCA; apply BetweenCollinear; trivial.
	     autoCollinear.
	   intro; elim H1; apply (InFLine F' D').
	     apply CollinearBAC;
	      apply (CollinearTrans (LineB F' D') A (LineA F' D') B H5).
	    apply CollinearBCA; apply FLineIn; trivial.
	    autoCollinear.
	   intro; elim H2; apply (InFLine F' D').
	     apply CollinearBAC;
	      apply (CollinearTrans (LineB F' D') A (LineA F' D') (LineA F D) H5).
	    apply CollinearBCA; apply FLineIn; trivial.
	    autoCollinear.
	   destruct (ExistsClockwiseParallelogrammSym (LineA F D) (LineB F D) C A E)
	    as (G, (H8, H9)).
	    apply (ParallelogrammSym (LineA F D) (LineB F D) A B C H H3 H4).
	    apply BetweenSym; trivial.
	    apply (TwoPointsSecantLines A G).
	     unfold Parallelogramm in *; intuition.
	     apply ClockwiseNotClockwise; trivial.
	     trivial.
	     apply (InFLine F' D').
	       apply CollinearBAC;
	        apply (CollinearTrans (LineB F' D') A (LineA F' D') G H5).
	      apply CollinearBCA; apply FLineIn; trivial.
	      apply CollinearBAC; apply (CollinearTrans A E).
	       intro; subst; elim (CollinearNotClockwiseABC (LineA F D) C E).
	        apply CollinearCAB; apply BetweenCollinear; trivial.
	        assert (H10 := EquiOrientedRev _ _ _ (BetweenSym _ _ _ H4)).
	          apply ClockwiseCAB; unfold Parallelogramm in *; intuition; canonize.
	          apply H10; autoClockwise.
	       autoCollinear.
	       trivial.
	   destruct (ExistsClockwiseParallelogramm _ _ _ _ E H H7) as (G, (H8, H9)).
	     apply (TwoPointsSecantLines A G).
	    unfold Parallelogramm in *; intuition.
	    apply ClockwiseNotClockwise; trivial.
	    trivial.
	    apply (InFLine F' D').
	      apply CollinearBAC;
	       apply (CollinearTrans (LineB F' D') A (LineA F' D') G H5).
	     apply CollinearBCA; apply FLineIn; trivial.
	     apply CollinearBAC; apply (CollinearTrans A E).
	      intro; subst; elim (CollinearNotClockwiseABC (LineA F D) E B).
	       apply CollinearCBA; apply BetweenCollinear; trivial.
	       unfold Parallelogramm in *; intuition.
	      autoCollinear.
	      trivial.
Qed.

Lemma ParallelogrammSuperimposed : forall A B C E : Point, forall F : Figure, forall D : Line F,
	Parallelogramm A B C E ->
	EquiDirected A B (LineA F D) (LineB F D) ->
	F C ->
	Superimposed F (Collinear C E).
Proof.
	intros.
	destruct (Apart (LineA F D) (LineB F D) C (LineH F D)).
	 decompose [or] (ThreeCases (LineA F D) C E).
	  elim
	   (SecantParallelogrammSecant C E (Collinear A B) F
	      (Ruler A B (ParallelogrammDistinctAB _ _ _ _ H)) D H H1).
	   intro; elim (ClockwiseNotCollinear _ _ _ H3).
	     apply
	      (CollinearTrans (LineA F D) (LineB F D) C E (LineH F D)
	         (FLineIn F D C H1) (FLineIn F D E H4)).
	   exact H0.
	  elim
	   (SecantParallelogrammSecant C E (Collinear A B) F
	      (Ruler A B (ParallelogrammDistinctAB _ _ _ _ H)) D H H1).
	   intro; elim (ClockwiseNotCollinear _ _ _ H4); apply CollinearBAC.
	     apply
	      (CollinearTrans (LineA F D) (LineB F D) C E (LineH F D)
	         (FLineIn F D C H1) (FLineIn F D E H3)).
	   exact H0.
	  apply LineAB; auto.
	   apply (ParallelogrammDistinctCD _ _ _ _ H).
	   apply (InFLine F D E);
	    apply
	     (CollinearTrans (LineA F D) C (LineB F D) E H2
	        (CollinearACB _ _ _ (FLineIn F D C H1)) H4).
	 decompose [or] (ThreeCases (LineB F D) C E).
	  elim
	   (SecantParallelogrammSecant C E (Collinear A B) F
	      (Ruler A B (ParallelogrammDistinctAB _ _ _ _ H)) D H H1).
	   intro; elim (ClockwiseNotCollinear _ _ _ H3).
	     apply
	      (CollinearTrans (LineB F D) (LineA F D) C E (sym_not_eq (LineH F D))
	         (CollinearBAC _ _ _ (FLineIn F D C H1))
	         (CollinearBAC _ _ _ (FLineIn F D E H4))).
	   exact H0.
	  elim
	   (SecantParallelogrammSecant C E (Collinear A B) F
	      (Ruler A B (ParallelogrammDistinctAB _ _ _ _ H)) D H H1).
	   intro; elim (ClockwiseNotCollinear _ _ _ H4); apply CollinearBAC.
	     apply
	      (CollinearTrans (LineB F D) (LineA F D) C E (sym_not_eq (LineH F D))
	         (CollinearBAC _ _ _ (FLineIn F D C H1))
	         (CollinearBAC _ _ _ (FLineIn F D E H3))).
	   exact H0.
	  apply LineAB; auto.
	   apply (ParallelogrammDistinctCD _ _ _ _ H).
	   apply (InFLine F D E); apply CollinearBAC.
	     apply
	      (CollinearTrans (LineB F D) C (LineA F D) E H2
	         (CollinearBCA _ _ _ (FLineIn F D C H1)) H4).
Qed.

End DISTINCT_PARALLEL.

