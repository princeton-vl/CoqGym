Require Export D4_CongruenceProp.

Section PARALLELOGRAMM_PROP.

Lemma ExistsDParallelogramm : forall A B C : Point,
	Clockwise A B C ->
	{D : Point | Parallelogramm A B C D}.
Proof.
	intros.
	assert (Hab := ClockwiseDistinctAB _ _ _ H).
	assert (Hbc := ClockwiseDistinctBC _ _ _ H).
	setCircle A B C Hbc ipattern:(F1) ipattern:(G1).
	setCircle C A B Hab ipattern:(F2) ipattern:(G2).
	setCinterclockC F1 F2 G1 G2 ipattern:(D) ipattern:(H1) ipattern:(H2) ipattern:(H3) ipattern:(H4).
	 rewrite (DistSym A C); apply TriangleSpecComm; try autoDistinct.
	   apply ClockwiseTriangleSpec; autoClockwise.
	 exists D; unfold Parallelogramm in |- *; intuition.
Qed.

Lemma ParallelogrammCenterClockwiseABI : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	Clockwise A B I.
Proof.
	unfold ParallelogrammCenter, Parallelogramm in |- *; intuition.
	apply ClockwiseBCA; apply (BetweenClockwiseMBC C A B I).
	 autoClockwise.
	 apply BetweenSym; trivial.
Qed.

Lemma ParallelogrammCenterClockwiseAID : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	Clockwise A I D.
Proof.
	unfold ParallelogrammCenter, Parallelogramm in |- *; intuition.
	apply (BetweenClockwiseAMC _ _ _ _ H0 H).
Qed.

Lemma ParallelogrammCenterClockwiseICD : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	Clockwise I C D.
Proof.
	unfold ParallelogrammCenter, Parallelogramm in |- *; intuition.
	apply (BetweenClockwiseMBC _ _ _ _ H0 H).
Qed.

Lemma ParallelogrammCenterClockwiseIBC : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	Clockwise I B C.
Proof.
	unfold ParallelogrammCenter, Parallelogramm in |- *; intuition.
	apply ClockwiseBCA; apply (BetweenClockwiseAMC C A B I).
	 autoClockwise.
	 apply BetweenSym; trivial.
Qed.

Lemma ParallelogrammCenterCongruentTriangles : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	CongruentStrictTriangles A I B C I D.
Proof.
	intros.
	assert (H1 := ParallelogrammCongruentTrianglesAC _ _ _ _ H).
	assert (H2 := ParallelogrammCenterClockwiseABI _ _ _ _ _ _ H0).
	unfold ParallelogrammCenter, Parallelogramm in *; intuition.
	apply CongruentStrictTrianglesSASA.
	 autoDistance.
	 autoDistance.
	 rewrite (BetweenAngleB A I B C).
	  rewrite (BetweenAngleB C I D A).
	   apply CongruentStrictTrianglesA.
	     apply (CongruentStrictTrianglesACB _ _ _ _ _ _ H1).
	   autoDistinct.
	   apply (BetweenSym _ _ _ H).
	  autoDistinct.
	  trivial.
	 intro; elim (ClockwiseNotCollinear _ _ _ H2); autoCollinear.
Qed.

Lemma ParallelogrammCenterBetweenBID : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	Between B I D.
Proof.
	intros.
	apply (SupplementaryRec I B A D).
	 apply ClockwiseBCA; apply (ParallelogrammCenterClockwiseABI _ _ _ _ _ H H0).
	 apply (ParallelogrammCenterClockwiseAID _ _ _ _ _ H H0).
	 assert (H1 := ParallelogrammCenterCongruentTriangles A B C D I H H0).
	   rewrite
	    (CongruentStrictTrianglesB _ _ _ _ _ _
	       (CongruentStrictTrianglesCBA _ _ _ _ _ _ H1)).
	   apply SupplementaryCommut.
	   exists I; exists A; exists D; exists C; intuition.
	  elim
	   (ClockwiseDistinctBC _ _ _
	      (ParallelogrammCenterClockwiseAID _ _ _ _ _ H H0) H2).
	  unfold ParallelogrammCenter in *; intuition.
Qed.

Lemma ParallelogrammCenterMidPointBD : forall A B C D I : Point, 
	forall H : Parallelogramm A B C D,
	ParallelogrammCenter A B C D H I ->
	Distance I B = Distance I D.
Proof.
	intros.
	assert (H1 := ParallelogrammCenterCongruentTriangles A B C D I H H0).
	apply (CongruentStrictTrianglesBC _ _ _ _ _ _ H1).
Qed.
	
Theorem ParallelHalfLine : forall A B C D E : Point, 
	forall H : Parallelogramm A B C D,
	HalfLine C D E ->
	Clockwise A B E.
Proof.
	intros.
	destruct (ExistsParallelogrammCenter A B C D H) as (I, H1).
	assert (H2 := ParallelogrammCenterClockwiseABI _ _ _ _ _ _ H1).
	assert (H3 := ParallelogrammCenterCongruentTriangles _ _ _ _ _ _ H1).
	assert (H4 := ParallelogrammCenterClockwiseICD _ _ _ _ _ _ H1).
	destruct (CentralSymetPoint E I) as (F, (H5, H6)).
 	intro; subst; elim (ClockwiseNotCollinear _ _ _ H4).
 	  apply CollinearCAB; apply (HalfLineCollinear _ _ _ H0).
 	assert (H7 : Clockwise C E I).
 	 apply H0; autoClockwise.
 	 assert (H8 : Clockwise F E A).
 	  apply (ClockwiseBetweenMBC F E A I).
 	   apply (BetweenSym _ _ _ H6).
 	   destruct H1.
 	     apply ClockwiseBCA; apply (EquiOrientedRev _ _ _ H1).
 	     autoClockwise.
 	  assert (CongruentStrictTriangles E I C F I A).
 	   unfold ParallelogrammCenter in H1; apply CongruentOpposedStrictTriangles.
 	    trivial.
 	    apply BetweenSym; intuition.
 	    autoDistance.
 	    intuition.
 	    intro; elim (ClockwiseNotCollinear _ _ _ H7); autoCollinear.
 	   trivial.
 	     assert (H10 : HalfLine A B F).
 	    apply (AngleBHalfLine A B I F).
 	     trivial.
 	     apply ClockwiseCAB; apply (BetweenClockwiseAMC F E A I).
 	      trivial.
 	      apply BetweenSym; trivial.
 	     rewrite
 	      (CongruentStrictTrianglesA _ _ _ _ _ _
 	         (CongruentStrictTrianglesACB _ _ _ _ _ _ H3)).
 	       rewrite <- (CongruentStrictTrianglesC _ _ _ _ _ _ H9).
 	       apply HalfLineAngleB.
 	      autoDistinct.
 	      autoDistinct.
 	      trivial.
 	    apply (HalfLineSym A B F).
 	     autoDistinct.
 	     trivial.
 	     autoClockwise.
 Qed.

Theorem HalfLineParallel : forall A B C D E : Point,
	forall H : Parallelogramm A B C D,
	HalfLine D C E ->
	Clockwise A B E.
Proof.
	intros.
	destruct (ExistsParallelogrammCenter A B C D H) as (I, H1).
	assert (H2 := ParallelogrammCenterClockwiseABI _ _ _ _ _ _ H1).
	assert (H3 := ParallelogrammCenterCongruentTriangles _ _ _ _ _ _ H1).
	assert (H4 := ParallelogrammCenterClockwiseICD _ _ _ _ _ _ H1).
	destruct (CentralSymetPoint E I) as (F, (H5, H6)).
	 intro; subst; elim (ClockwiseNotCollinear _ _ _ H4).
	   apply CollinearCBA; apply (HalfLineCollinear _ _ _ H0).
	 assert (H7 : Clockwise E D I).
	  generalizeChangeSense.
	    apply H6; autoClockwise.
	  assert (H8 : Clockwise E F B).
	   apply (ClockwiseBetweenAMC E F B I).
	    trivial.
	    assert
	     (H8 := BetweenSym _ _ _ (ParallelogrammCenterBetweenBID _ _ _ _ _ _ H1)).
	      apply ClockwiseCAB; canonize.
	      apply H11; autoClockwise.
	   assert (CongruentStrictTriangles D I E B I F).
	    unfold ParallelogrammCenter in H1; apply CongruentOpposedStrictTriangles.
	     apply (BetweenSym B I D (ParallelogrammCenterBetweenBID A B C D I H H1)).
	     trivial.
	     assert (H9 := ParallelogrammCenterMidPointBD A B C D I H H1); auto.
	     autoDistance.
	     intro; elim (ClockwiseNotCollinear _ _ _ H7); autoCollinear.
	    assert (H10 : HalfLine B A F).
	     apply (AngleCHalfLine B I A F).
	      autoClockwise.
	      apply ClockwiseCAB; apply (BetweenClockwiseMBC E F B I); trivial.
	      rewrite
	       (CongruentStrictTrianglesB _ _ _ _ _ _
	          (CongruentStrictTrianglesBCA _ _ _ _ _ _ H3)).
	        rewrite <- (CongruentStrictTrianglesA _ _ _ _ _ _ H9).
	        apply HalfLineAngleC.
	       autoDistinct.
	       autoDistinct.
	       trivial.
	     generalizeChangeSide.
	       apply H12.
	      autoDistinct.
	      autoClockwise.
Qed.

Theorem ParallelClockwise : forall A B C : Point,
	Clockwise A B C ->
	exists D : Point, EquiDirected A B C D /\ C <> D.
Proof.
	intros.
	destruct (ExistsDParallelogramm _ _ _ H) as (D, H0).
	exists D; canonize.
	 do 6 right; left; intros E H4.
	   destruct (FourPointsIntersectionPoint C D A E) as (F, (H5, H6)).
	  unfold Parallelogramm in *; autoClockwise.
	  trivial.
	  apply ClockwiseBCA; apply (ClockwiseBetweenMBC E A B F).
	   apply BetweenSym; trivial.
	   destruct (CollinearHalfLine _ _ _ H5).
	    apply ClockwiseCAB; apply (ParallelHalfLine A B C D F H0 H1).
	    apply ClockwiseCAB; apply (HalfLineParallel A B C D F H0 H1).
	 unfold Parallelogramm in *; intuition.
	   autoDistinct.
Qed.

Lemma ParallelogrammParallelogrammBetween : forall A B C D E : Point,
	Parallelogramm A B C D ->
	Parallelogramm C A B E ->
	Between D C E.
Proof.
	intros; apply (SumAngles C D A B E).
	 unfold Parallelogramm in *; intuition; autoClockwise.
	 unfold Parallelogramm in *; intuition; autoClockwise.
	 unfold Parallelogramm in *; intuition; autoClockwise.
	 apply sym_eq; rewrite (AngleSym A C B).
	  apply CongruentStrictTrianglesB.
	    apply CongruentStrictTrianglesBAC;
	     apply (ParallelogrammCongruentTrianglesAC _ _ _ _ H).
	  apply (ParallelogrammDistinctAC _ _ _ _ H).
	  apply (ParallelogrammDistinctAB _ _ _ _ H).
	 apply sym_eq; apply CongruentStrictTrianglesC.
	   apply (ParallelogrammCongruentTrianglesAC _ _ _ _ H0).
Qed.

Lemma ParallelogrammClockwiseBCD : forall A B C D : Point,
	Parallelogramm A B C D ->
	Clockwise B C D.
Proof.
	intros; destruct (ExistsParallelogrammCenter _ _ _ _ H) as (I, H0).
	apply ClockwiseBCA; apply (ClockwiseBetweenMBC D B C I).
	 apply BetweenSym; apply (ParallelogrammCenterBetweenBID _ _ _ _ _ H H0).
	 apply (ParallelogrammCenterClockwiseIBC _ _ _ _ _ H H0).
Qed.

Lemma ParallelogrammClockwiseBDA : forall A B C D : Point,
	Parallelogramm A B C D ->
	Clockwise B D A.
Proof.
	intros; destruct (ExistsParallelogrammCenter _ _ _ _ H) as (I, H0).
	apply (ClockwiseBetweenAMC B D A I).
	 apply (ParallelogrammCenterBetweenBID _ _ _ _ _ H H0).
	 apply ClockwiseBCA; apply (ParallelogrammCenterClockwiseABI _ _ _ _ _ H H0).
Qed.

Lemma ParallelogrammPermut : forall A B C D : Point,
	Parallelogramm A B C D ->
	Parallelogramm B C D A.
Proof.
	intros; unfold Parallelogramm in |- *; intuition.
	 apply (ParallelogrammClockwiseBCD _ _ _ _ H).
	 apply (ParallelogrammClockwiseBDA _ _ _ _ H).
	 unfold Parallelogramm in *; intuition; autoDistance.
	 unfold Parallelogramm in *; intuition; autoDistance.
Qed.

Lemma ParallelogrammSym : forall A B C D E : Point,
	Parallelogramm A B C D ->
	Distance D C = Distance C E ->
	Between D C E ->
	Parallelogramm A B E C.
Proof.
	intros.
	destruct (ExistsDParallelogramm C A B) as (F, H2).
	 unfold Parallelogramm in *; intuition; autoClockwise.
	 assert (H3 : E = F).
	  apply (HalfLineEquidistantEqual C E F).
	   apply (BetweenDistinctBC _ _ _ H1).
	   assert (H3 := ParallelogrammParallelogrammBetween _ _ _ _ _ H H2).
	     assert (H4 := EquiOrientedRev _ _ _ H1); canonize.
	   unfold Parallelogramm in *; intuition; autoDistance.
	  rewrite H3; apply (ParallelogrammPermut _ _ _ _ H2).
Qed.

End PARALLELOGRAMM_PROP.
