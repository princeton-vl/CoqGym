Require Export C7_DroitesSecantesProp.

Section PARALLEL_SUPERIMPOSED.

Lemma EquiDirectedCollinearEquiDirected : forall A B C D E : Point,
	EquiDirected A B C D ->
	Collinear C D E ->
	C <> D ->
	C <> E ->
	EquiDirected A B C E.
Proof.
	intros.
	destruct (ExclusiveTwoCases _ _ _ H2 H0).
	 generalizeChange.
	 assert (H4 := EquiOrientedSym C D E H1 H3).
	   generalizeChange.
Qed.

Lemma EquiDirectedCollinearCollinearEquiDirected : forall A B C D E F : Point,
	EquiDirected A B C D ->
	Collinear C D E ->
	C <> D ->
	Collinear C D F ->
	E <> F ->
	EquiDirected A B E F.
Proof.
	intros.
	destruct (Apart C D E H1).
	 apply (EquiDirectedCollinearEquiDirected A B E C F).
	  apply EquiDirectedPermutCD;
	   apply (EquiDirectedCollinearEquiDirected A B C D E H H0 H1 H4).
	  apply CollinearBAC; apply (CollinearTrans C D E F H1 H0 H2).
	  auto.
	  trivial.
	 apply (EquiDirectedCollinearEquiDirected A B E D F).
	  apply EquiDirectedPermutCD;
	   apply (EquiDirectedCollinearEquiDirected A B D C E).
	   apply EquiDirectedPermutCD; trivial.
	   autoCollinear.
	   auto.
	   trivial.
	  apply CollinearBAC; apply (CollinearTrans D C E F); autoCollinear.
	  auto.
	  trivial.
Qed.

Lemma TwoPointsSecantLines : forall A B : Point, forall F F' : Figure, forall D : Line F, forall D' : Line F',
	Clockwise (LineA F D) (LineB F D) A ->
	~Clockwise (LineA F D) (LineB F D) B ->
	F' A ->
	F' B ->
	SecantLines F F' D D'.
Proof.
	intros.
	unfold SecantLines, ParallelLines in |- *.
	intro; elim (FourPointsSecantLine (LineA F D) (LineB F D) A B H H0).
	apply (EquiDirectedCollinearCollinearEquiDirected _ _ _ _ A B H3).
	 apply FLineIn; trivial.
	 apply LineH.
	 apply FLineIn; trivial.
	 intro; elim H0; subst; auto.
Qed.

Lemma EquiDirectedLineACollinear : forall A : Point, forall F F' : Figure, forall D : Line F, forall D' : Line F',
	EquiDirected (LineA F D) (LineB F D) (LineA F' D') (LineB F' D') ->
	F A ->
	F' A ->
	LineA F D <> A ->
	F' (LineA F D).
Proof.
	intros.
	decompose [or] (ThreeCases (LineA F' D') (LineB F' D') (LineA F D)).
	 elim (FourPointsSecantLine (LineA F' D') (LineB F' D') (LineA F D) A H3).
	  apply CollinearNotClockwiseABC; apply FLineIn; trivial.
	  apply
	   (EquiDirectedCollinearEquiDirected (LineA F' D') 
	      (LineB F' D') (LineA F D) (LineB F D) A).
	   apply EquiDirectedSym; trivial.
	   apply FLineIn; trivial.
	   apply LineH.
	   trivial.
	 elim (FourPointsSecantLine (LineB F' D') (LineA F' D') (LineA F D) A H4).
	  apply CollinearNotClockwiseBAC; apply FLineIn; trivial.
	  apply EquiDirectedPermut;
	   apply
	    (EquiDirectedCollinearEquiDirected (LineA F' D') 
	       (LineB F' D') (LineA F D) (LineB F D) A).
	   apply EquiDirectedSym; trivial.
	   apply FLineIn; trivial.
	   apply LineH.
	   trivial.
	 apply (InFLine F' D'); trivial.
Qed.

Lemma EquiDirectedLineBCollinear : forall A : Point, forall F F' : Figure, forall D : Line F, forall D' : Line F',
	EquiDirected (LineA F D) (LineB F D) (LineA F' D') (LineB F' D') ->
	F A ->
	F' A ->
	LineB F D <> A ->
	F' (LineB F D).
Proof.
	intros.
	decompose [or] (ThreeCases (LineA F' D') (LineB F' D') (LineB F D)).
	 elim (FourPointsSecantLine (LineA F' D') (LineB F' D') (LineB F D) A H3).
	  apply CollinearNotClockwiseABC; apply FLineIn; trivial.
	  apply
	   (EquiDirectedCollinearEquiDirected (LineA F' D') 
	      (LineB F' D') (LineB F D) (LineA F D) A).
	   apply EquiDirectedSym; apply EquiDirectedPermut; trivial.
	   apply CollinearBAC; apply FLineIn; trivial.
	   apply sym_not_eq; apply LineH.
	   trivial.
	 elim (FourPointsSecantLine (LineB F' D') (LineA F' D') (LineB F D) A H4).
	  apply CollinearNotClockwiseBAC; apply FLineIn; trivial.
	  apply EquiDirectedPermut;
	   apply
	    (EquiDirectedCollinearEquiDirected (LineA F' D') 
	       (LineB F' D') (LineB F D) (LineA F D) A).
	   apply EquiDirectedSym; apply EquiDirectedPermut; trivial.
	   apply CollinearBAC; apply FLineIn; trivial.
	   apply sym_not_eq; apply LineH.
	   trivial.
	 apply (InFLine F' D'); trivial.
Qed.

Lemma CollinearSuperimposed : forall A : Point, forall F F' : Figure, forall D : Line F, forall D' : Line F',
	EquiDirected (LineA F D) (LineB F D) (LineA F' D') (LineB F' D') ->
	F A ->
	F' A ->
	Superimposed F F'.
Proof.
	intros.
	destruct (Apart (LineA F D) (LineB F D) A (LineH F D)).
	 apply (SuperimposedTrans F (Collinear A (LineA F D)) F').
	  apply (LineAB A (LineA F D) F D (sym_not_eq H2) H0 (FLineA F D)).
	  apply SuperimposedSym;
	   apply (LineAB A (LineA F D) F' D' (sym_not_eq H2) H1).
	    apply (EquiDirectedLineACollinear A F F' D D' H H0 H1 H2).
	 apply (SuperimposedTrans F (Collinear A (LineB F D)) F').
	  apply (LineAB A (LineB F D) F D (sym_not_eq H2) H0 (FLineB F D)).
	  apply SuperimposedSym;
	   apply (LineAB A (LineB F D) F' D' (sym_not_eq H2) H1).
	    apply (EquiDirectedLineBCollinear A F F' D D' H H0 H1 H2).
Qed.

End PARALLEL_SUPERIMPOSED.
