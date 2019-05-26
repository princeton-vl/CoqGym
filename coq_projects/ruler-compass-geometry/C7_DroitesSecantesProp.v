Require Export C6_Parallele_Prop.

Section SECANT_LINES_PROPERTIES.

Lemma  StrictlyParallel : forall A B C D,
	EquiOriented A B C D ->
	~Collinear A B C ->
	~Collinear A B D.
Proof.
	intros A B C D H Hn H0; elim Hn.
	exact (ParallelCollinearABC A B C D H H0).
Qed.

Lemma NotClockwiseTwoCases : forall A B C : Point,
	~Clockwise A B C ->
	Clockwise B A C \/ Collinear A B C.
Proof.
	intros; decompose [or] (FourCases A B C); intuition.
	 right; apply HalfLineCollinear; trivial.
	 right; apply CollinearBAC; apply HalfLineCollinear; trivial.
Qed.

Lemma FourPointsSecantLine : forall A B C D,
	Clockwise A B C ->
	~Clockwise A B D ->
	~EquiDirected A B C D.
Proof.
	intros.
	assert (Hcd : C <> D).
	 intro; subst; elim H0; trivial.
	 generalizeChange.
	  elim (NotClockwiseABA C D); autoClockwise.
	  elim (NotClockwiseBAA C D); autoClockwise.
	  destruct (NotClockwiseTwoCases _ _ _ H0).
	   elim (NotClockwiseBAA D C); auto.
	   elim (ClockwiseNotCollinear A B C H); apply CollinearBAC.
 	    apply (ParallelCollinearABC B A C D H2); autoCollinear.
	  destruct (NotClockwiseTwoCases _ _ _ H0).
	   elim (NotClockwiseABA D C); auto.
	   elim (ClockwiseNotCollinear A B C H); apply CollinearBAC.
	     apply (ParallelCollinearABD B A D C H1); autoCollinear.
	  destruct (NotClockwiseTwoCases _ _ _ H0).
	   elim (NotClockwiseABA D C); auto.
	   elim (ClockwiseNotCollinear A B C H); apply CollinearBAC.
	     apply (ParallelCollinearABD B A D C H3); autoCollinear.
	  elim (NotClockwiseBAA C D); autoClockwise.
	  destruct (NotClockwiseTwoCases _ _ _ H0).
	   elim (NotClockwiseBAA D C); auto.
	   elim (ClockwiseNotCollinear A B C H); apply CollinearBAC.
	     apply (ParallelCollinearABC B A C D H3); autoCollinear.
	  elim (NotClockwiseABA C D); autoClockwise.
Qed.

Lemma NotEquidirectedDistinctAB : forall A B C D,
	~EquiDirected A B C D-> 
	A<>B.
Proof.
	canonize.
	elim H1; intros E H9.
	elim (ClockwiseDistinctAB A B E H9); trivial.
Qed.

Lemma NotEquidirectedDistinctCD : forall A B C D,
	~EquiDirected A B C D-> 
	C<>D.
Proof.
	canonize.
	elim H4; intros E H9.
	elim (ClockwiseDistinctAB C D E H9); trivial.
Qed.

Lemma LinesIntersectionPoint : forall A B C D,
	~EquiDirected A B C D-> 
	{I : Point | Collinear A B I /\ Collinear C D I}.
Proof.
	intros.
	setLine A B (NotEquidirectedDistinctAB A B C D H) ipattern:(F1) ipattern:(L1).
	setLine C D (NotEquidirectedDistinctCD A B C D H) ipattern:(F2) ipattern:(L2).
	setLinterL F1 F2 L1 L2 ipattern:(J) ipattern:(H2) ipattern:(H3) ipattern:(H4).
	 unfold SecantLines , F1, F2, L1, L2 in |- *; simpl in |- *; trivial.
	 exists J; intuition.
Qed.

Lemma UniqueIntersectionLines : forall A B C D I J : Point,
	A <> B ->
	C <> D ->
	~EquiDirected A B C D ->
	Collinear A B I ->
	Collinear A B J ->
	Collinear C D I ->
	Collinear C D J ->
	I = J.
Proof.
	intros.
	setLine A B H ipattern:(F1) ipattern:(L1).
	setLine C D H0 ipattern:(F2) ipattern:(L2).
	setLinterL F1 F2 L1 L2 ipattern:(E) ipattern:(H6) ipattern:(H7) ipattern:(H8).
	 trivial.
	 unfold Unicity in *.
	   rewrite <- (H8 I).
	  apply H8.
	    intuition.
	  intuition.
Qed.

Lemma FourPointsIntersectionPoint : forall A B C D,
	Clockwise A B C ->
	Clockwise B A D ->
	{I : Point | Collinear A B I /\ Between C I D}.
Proof.
	intros A B C D H H0;
	 destruct (LinesIntersectionPoint A B C D) as (E, (H1, H2)).
	 apply FourPointsSecantLine; autoClockwise.
	 exists E; canonize.
	  subst; autoClockwise.
	  destruct (ExclusiveCollinear E D C).
	   apply (CollinearClockwiseDistinct B A E D); canonize.
	   autoDistinct.
	   apply CollinearCAB; autoClockwise.
	     destruct (CollinearHalfLine A B E).
	    autoClockwise.
	    canonize.
	      elim (ClockwiseNotClockwise C E A).
	     generalizeChangeSense.
	       apply H7; apply ClockwiseCAB; auto.
	     apply ClockwiseBCA; auto.
	    canonize.
	      elim (ClockwiseNotClockwise E C B).
	     apply H6; apply ClockwiseBCA; auto.
	     apply ClockwiseCAB; generalizeChange.
	   canonize.
Qed.

Lemma PaschABC  : forall A B C M N,
	Clockwise A B C ->
	Between A M B  ->
	~Collinear A M N ->
	~Collinear B M N ->
	~Collinear C M N ->
	(exists P : Point, Collinear M N P /\ Between A P C) \/
	(exists P : Point, Collinear M N P /\ Between B P C).
Proof.
	intros A B C M N H (H0, H1) H2 H3 H4.
	decompose [or] (ThreeCases A M N).
	 clear H2; decompose [or] (ThreeCases B M N).
	  clear H3 H4; elim (ClockwiseNotClockwise B M N); canonize.
	  clear H3; decompose [or] (ThreeCases C M N).
	   clear H4; destruct (FourPointsIntersectionPoint N M B C) as (P, (H3, H4)).
	    autoClockwise.
	    autoClockwise.
	    right; exists P; canonize.
	   clear H4; destruct (FourPointsIntersectionPoint M N A C) as (P, (H2, H4)).
	    autoClockwise.
	    autoClockwise.
	    left; exists P; canonize.
	   canonize.
	  canonize.
	 clear H2; decompose [or] (ThreeCases B M N).
	  clear H3; decompose [or] (ThreeCases C M N).
	   clear H4; destruct (FourPointsIntersectionPoint N M A C) as (P, (H5, H4)).
	    autoClockwise.
	    autoClockwise.
	    left; exists P; canonize.
	   clear H4; destruct (FourPointsIntersectionPoint M N B C) as (P, (H3, H4)).
	    autoClockwise.
	    autoClockwise.
	    right; exists P; canonize.
	   canonize.
	  clear H3 H4; assert (EquiOriented M B A M).
	   apply EquiOrientedRev; canonize.
	   elim (ClockwiseNotClockwise M A N); canonize.
	  canonize.
	 canonize.
Qed.

End SECANT_LINES_PROPERTIES.
