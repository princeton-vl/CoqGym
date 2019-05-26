Require Export B6_Cercle_Def.

Section EQUILATERAL_TRIANGLE.

Definition Equilateral (A B C : Point) :=
	Distance A B = Distance A C /\
	Distance A B = Distance B C.

Lemma DegeneratedEquilateral : forall A : Point,
	Equilateral A A A.
Proof.
	intro; split; auto.
Qed.

Lemma Exists2AB : forall A B : Point,
	A <> B ->
	{C : Point |
		Between A B C /\
		Distance B C = Distance A B}.
Proof.
	intros A B Hab.
	setLine A B Hab ipattern:(L) ipattern:(AB).
	setCircle B A B Hab ipattern:(G) ipattern:(BAB).
	setLinterposC L G AB BAB ipattern:(C) ipattern:(H1) ipattern:(H2) ipattern:(H3) ipattern:(H4).
	 apply CollinearABB.
	 exists C; canonize.
Qed.

Lemma EquilateralLSlt : forall A B : Point,
	A<>B -> LSlt (Distance A B) (LSplus (Distance A B) (Distance A B)).
Proof.
	intros A B H; destruct (Exists2AB A B H) as (C, (H0, H1)).
	pattern (Distance A B) at -3 in |- *; rewrite <- H1.
	rewrite (DistSym A B); rewrite (DistSym B C).
	rewrite Chasles.
	 apply OrderLSlt.
	  auto.
	  generalizeChangeSide.
	 apply (BetweenSymHalfLine _ _ _ H0).
	 apply (BetweenHalfLine _ _ _ H0).
Qed.

Lemma EquilateralSpec : forall A B : Point,
	A<>B -> TriangleSpec (Distance A B) (Distance A B) (Distance A B).
Proof.
	unfold TriangleSpec in |- *; intuition; apply EquilateralLSlt; auto.
Qed.

Lemma EquilateralClockwise : forall A B : Point,
	A <> B ->
	{C : Point | Equilateral A B C /\ Clockwise A B C}.
Proof.
	intros.
	setCircle A A B H ipattern:(C1) ipattern:(H1).
	setCircle B A B H ipattern:(C2) ipattern:(H2).
	setCinterclockC C1 C2 H1 H2 ipattern:(C) ipattern:(H3) ipattern:(H4) ipattern:(H5)
	 ipattern:(H6); unfold C1, C2, H1, H2 in *; simpl in *.
	 apply EquilateralSpec; auto.
	 exists C; unfold Equilateral in |- *; intuition.
Defined.

Lemma ClockwiseExists : forall A B : Point,
	A <> B ->
	{C : Point | Clockwise A B C}.
Proof.
	intros A B H; destruct (EquilateralClockwise A B H) as (C, (H1, H2)).
	exists C; trivial.
Qed.

Lemma ThirdPoint : {Vv : Point | Clockwise Oo Uu Vv}.
Proof.
	exact (ClockwiseExists Oo Uu DistinctOoUu).
Qed.

Lemma  Apart : forall A B C : Point, 
	A <> B -> A <> C \/ B <> C.
Proof.
	intros A B C H; decompose [or] (FourCases A B C).
	 right; exact (ClockwiseDistinctBC A B C H0).
	 left; exact (ClockwiseDistinctBC B A C H1).
	 canonize.
	   destruct (ClockwiseExists A B H) as (E, H1).
	   left; exact (ClockwiseDistinctAB A C E (H0 E H1)).
	 canonize.
	   destruct (ClockwiseExists B A (sym_not_eq H)) as (E, H1).
	   right; exact (ClockwiseDistinctAB B C E (H0 E H1)).
Qed.

End EQUILATERAL_TRIANGLE.
