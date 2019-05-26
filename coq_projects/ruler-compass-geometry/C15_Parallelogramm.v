Require Export C14_Angle_Droit.

Section PARALLELOGRAMM.

Definition Parallelogramm := fun A B C D : Point =>
	Clockwise A B C /\
	Clockwise A C D /\
	Distance A B = Distance C D /\
	Distance A D = Distance B C.

Lemma ParallelogrammCongruentTrianglesAC : forall A B C D : Point,
	Parallelogramm A B C D ->
	CongruentStrictTriangles A B C C D A.
Proof.
	intros A B C D (H1, (H2, (H3, H4))); repeat split; try autoDistance.
	elim (ClockwiseNotCollinear _ _ _ H1 H).
Qed.

Lemma ParallelogrammCongruentTrianglesBD : forall A B C D : Point,
	Parallelogramm A B C D ->
	CongruentTriangles D A B B C D.
Proof.
	intros A B C D (H1, (H2, (H3, H4))); repeat split; try autoDistance.
Qed.

Definition ParallelogrammCenter (A B C D : Point) (_ : Parallelogramm A B C D) :=
fun I : Point => Between A I C /\ Distance I A = Distance I C.

Lemma ExistsParallelogrammCenter : forall A B C D : Point, 
	forall H : Parallelogramm A B C D,
	{I : Point | ParallelogrammCenter A B C D H I}.
Proof.
	intros.
	assert (Hac : A <> C).
	 unfold Parallelogramm in H; decompose [and] H; autoDistinct.
	 exists (MidPoint A C Hac); split.
	  apply MidPointBetween.
	  unfold MidPoint in |- *.
	    destruct (ExistsMiddle A C Hac) as (I, (H1, H2)).
	    trivial.
Qed.

Lemma ParallelogrammDistinctAB : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> B.
Proof.
	unfold Parallelogramm in |- *; intuition.
	apply (ClockwiseDistinctAB _ _ _ H1 H0).
Qed.

Lemma ParallelogrammDistinctAC : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> C.
Proof.
	unfold Parallelogramm in |- *; intuition.
	apply (ClockwiseDistinctAB _ _ _ H H0).
Qed.

Lemma ParallelogrammDistinctCD : forall A B C D : Point,
	Parallelogramm A B C D ->
	C <> D.
Proof.
	unfold Parallelogramm in |- *; intuition.
	apply (ClockwiseDistinctBC _ _ _ H H0).
Qed.

End PARALLELOGRAMM.
