Require Export D7_NonParalleles_Secantes.

Section INCIDENCE.

(* I1 : For any two distinct points A, B, there exists a unique line L containing A, B. *)

Lemma I1 : forall A B : Point, exists L : Figure, exists D : Line L, L A /\ L B.
Proof.
	intros; destruct (Apart Oo Uu A DistinctOoUu).
	 decompose [or] (ThreeCases Oo A B).
	  setLine A B (ClockwiseDistinctBC Oo A B H0) L D.
	    exists L; exists D; unfold L in |- *; split.
	   apply CollinearABA.
	   apply CollinearABB.
	  setLine B A (ClockwiseDistinctCA A Oo B H1) L D.
	    exists L; exists D; unfold L in |- *; split.
	   apply CollinearABB.
	   apply CollinearABA.
	  setLine Oo A H L D.
	    exists L; exists D; unfold L in |- *; split.
	   apply CollinearABB.
	   trivial.
	 decompose [or] (ThreeCases Uu A B).
	  setLine A B (ClockwiseDistinctBC Uu A B H0) L D.
	    exists L; exists D; unfold L in |- *; split.
	   apply CollinearABA.
	   apply CollinearABB.
	  setLine B A (ClockwiseDistinctCA A Uu B H1) L D.
	    exists L; exists D; unfold L in |- *; split.
	   apply CollinearABB.
	   apply CollinearABA.
	  setLine Uu A H L D.
	    exists L; exists D; unfold L in |- *; split.
	   apply CollinearABB.
	   trivial.
Qed.

Lemma I1' : forall A B : Point, forall F1 F2 : Figure, forall D1 : Line F1, forall D2 : Line F2, 
	A <> B ->
	F1 A ->
	F1 B ->
	F2 A ->
	F2 B ->
	Superimposed F1 F2.
Proof.
	intros; apply SuperimposedTrans with (F2 := Collinear A B).
	 apply LineAB; auto.
	 apply SuperimposedSym; apply LineAB; auto.
Qed.

(* I2 : Every line contains at least two points. *)

Lemma I2 : forall F : Figure, forall D : Line F, exists A : Point, exists B : Point, A <> B /\ F A /\ F B.
Proof.
	intros.
	exists (LineA F D); exists (LineB F D); split.
	 exact (LineH F D).
	 split.
	  apply FLineA.
	  apply FLineB.
Qed.

(* I3 : There exist three noncollinear points (that is, three points not all contained in a single line). *)

Lemma I3 : exists A : Point, exists B : Point, exists C : Point, forall F : Figure, forall D : Line F, ~(F A /\ F B /\ F C).
Proof.
	exists Oo; exists Uu; exists Vv; intros F D (Ha, (Hb, Hc)).
	assert (HD := LineAB Oo Uu F D DistinctOoUu Ha Hb).
	destruct HD as (H1, H2).
	elim (ClockwiseNotCollinear _ _ _ ClockwiseUuOoVv).
	apply CollinearBAC; apply (H1 Vv Hc).
Qed.

End INCIDENCE.

