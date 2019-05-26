Require Export C4_Triangles_non_degeneres_egaux.

Section LINE_PROPERTIES.

Lemma ThreeCases : forall A B C,
	Clockwise A B C \/ Clockwise B A C \/ Collinear A B C.
Proof.
	intros; decompose [or] (FourCases A B C); canonize.
	 generalize (HalfLineCollinear A B C H); canonize.
	 generalize (HalfLineCollinear B A C H); canonize.
Qed.

Lemma InOrOutLine : forall A : Point, forall F : Figure, forall D : Line F,
	F A \/ ~F A.
Proof.
	intros; decompose [or] (ThreeCases (LineA F D) (LineB F D) A).
	 right; intro; elim (ClockwiseNotCollinear _ _ _ H).
	   apply FLineIn; trivial.
	 right; intro; elim (ClockwiseNotCollinear _ _ _ H0).
	   apply CollinearBAC; apply FLineIn; trivial.
	 left; apply (InFLine F D A); trivial.
Qed.

Lemma CollinearHalfLine : forall A B C,
        Collinear A B C ->
        HalfLine A B C \/ HalfLine B A C.
Proof.
	intros; decompose [or] (FourCases A B C); canonize.
Qed.

Lemma ExclusiveTwoCases : forall A B C,
	A <> C ->
	Collinear A B C ->
	HalfLine A B C \/
	EquiOriented A B C A.
Proof.
	intros A B C H H0; decompose [or] (ExclusiveFourCases A B C H); canonize.
Qed.

Lemma EquiOrientedSym : forall A B C,
	A<>B -> EquiOriented A B C A -> EquiOriented C A A B.
Proof.
	intros A B C H H0; generalize (EquiOrientedCollinear A B C H0); intro H1.
	destruct (CollinearHalfLine A B C H1).
	 canonize.
	   destruct (ClockwiseExists A B H) as (D, H5).
	   elim (ClockwiseNotClockwise A C D (H2 D H5)); auto.
	 destruct (CollinearHalfLine A C B (CollinearACB A B C H1)).
	  canonize.
	    destruct
	     (ClockwiseExists A C (sym_not_eq (ClockwiseDistinctAB C A x H1)))
	     as (D, H6).
	    elim (ClockwiseNotClockwise A C D H6); auto.
	  generalizeChange.
Qed.

Lemma EquiOrientedRev : forall A B C,
	Between A B C -> EquiOriented B C A B.
Proof.
	canonize.
	destruct (ExclusiveTwoCases B C A).
	 auto.
	 apply CollinearBCA; apply BetweenCollinear; canonize.
	 destruct (ClockwiseExists A B H0) as (D, H3).
	   elim (ClockwiseNotClockwise A B D); canonize.
	 canonize.
Qed.

Lemma BetweenTransC : forall A B C D : Point,
	Between A B C ->
	Between A C D ->
	Between B C D.
Proof.
	intros.
	assert (H1 := BetweenHalfLine A B C H).
	assert (H2 := EquiOrientedRev A B C H).
	assert (H3 := BetweenDistinctBC A B C H).
	generalizeChange.
Qed.

Lemma BetweenTransA : forall A B C D : Point,
	Between A B C ->
	Between A C D ->
	Between A B D.
Proof.
	intros.
	apply (BetweenAssocLeft A B C D); auto.
	apply (BetweenTransC A B C D); auto.
Qed.

Lemma NotFourBetween : forall A B C M P Q : Point,
	Clockwise A M P ->
	Between A M B ->
	Between A P C ->
	Between B Q C ->
	Between M P Q ->
	False.
Proof.
	intros; elim (ClockwiseNotClockwise A M P H).
	generalize (EquiOrientedRev A M B H0); generalize (EquiOrientedRev A P C H1);
	 generalize (EquiOrientedRev B Q C H2); generalize (EquiOrientedRev M P Q H3);
	 generalizeChange.
	apply H20; apply ClockwiseCAB.
	apply H4; apply ClockwiseCAB.
	apply H15; apply ClockwiseCAB.
	apply H3.
	 apply (BetweenDistinctBC M P Q); canonize.
	 apply ClockwiseBCA.
	   apply H9.
	  apply (BetweenDistinctBC A P C); canonize.
	  apply ClockwiseCAB; trivial.
Qed.

Lemma ExclusiveCollinear : forall A B C,
        A <> B ->
	A <> C -> 
        Collinear A B C ->
        HalfLine A B C \/ Between C A B.
Proof.
	intros A B C H H0 H1; destruct (ExclusiveTwoCases A B C H0 H1).
	 auto.
	 right; split.
	  auto.
	  apply EquiOrientedSym; auto.
Qed.

Lemma CollinearTrans : forall A B C D,
        A <> B ->
        Collinear A B C ->
        Collinear A B D ->
	Collinear A C D.
Proof.
	canonize.
	 destruct (ExclusiveTwoCases A C B); canonize.
	  elim H3; autoClockwise.
	  elim H2; autoClockwise.
	 destruct (ExclusiveTwoCases A D B); canonize.
	  elim H4; autoClockwise.
	  elim H0; autoClockwise.
	  elim H2; apply H5; autoClockwise.
	  elim H3; apply H5; autoClockwise.
Qed.

Lemma MarkChange : forall A B C D,
	A <> B ->
	C <> D ->
	Collinear A B C ->
	Collinear A B D ->
	Superimposed (Collinear A B) (Collinear C D).
Proof.
	intros; destruct (Apart C D A H0); split; do 3 red in |- *; intros E H4.
	 apply (CollinearTrans C A D E H3).
	  apply CollinearBAC; apply (CollinearTrans A B C D H); trivial.
	  apply CollinearBAC; apply (CollinearTrans A B C E H); trivial.
	 apply (CollinearTrans A C B E (sym_not_eq H3)).
	  apply CollinearACB; trivial.
	  apply CollinearBAC; apply (CollinearTrans C D A E H0).
	   apply CollinearBCA; apply (CollinearTrans A B C D H); trivial.
	   trivial.
	 apply CollinearBAC; apply (CollinearTrans D A C E H3).
	  apply CollinearBAC; apply (CollinearTrans A B D C H); trivial.
	  apply CollinearBAC; apply (CollinearTrans A B D E H); trivial.
	 apply (CollinearTrans A D B E (sym_not_eq H3)).
	  apply CollinearACB; trivial.
	  apply CollinearBAC; apply (CollinearTrans D C A E (sym_not_eq H0)).
	   apply CollinearCBA; apply (CollinearTrans A B C D H); trivial.
	   apply CollinearBAC; trivial.
Qed.

Lemma LineAB : forall A B : Point, forall F : Figure, forall D : Line F, 
	A <> B ->
	F A ->
	F B ->
	Superimposed F (Collinear A B).
Proof.
	intros; assert (H2 := LineSuperimposedAB F D).
	apply SuperimposedTrans with (F2 := Collinear (LineA F D) (LineB F D)); auto.
	inversion H2; apply MarkChange; auto.
	 apply LineH.
	 apply H3; auto.
	 apply H3; auto.
Qed.

End LINE_PROPERTIES.

