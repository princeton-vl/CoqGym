Require Export C2_Entre_Prop.

Section CONGRUENT_TRIANGLES.

Definition CongruentTriangles (A B C A' B' C' : Point) :=
	Distance A B = Distance A' B' /\
	Distance B C = Distance  B' C' /\
	Distance C A = Distance C' A'.

Lemma CongruentTrianglesSym : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	CongruentTriangles A' B' C' A B C.
Proof.
	unfold CongruentTriangles in |- *; intuition.
Qed.

Lemma CongruentTrianglesBAC : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	CongruentTriangles B A C B' A' C'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
	 rewrite DistSym; rewrite H0; apply DistSym.
	 rewrite DistSym; rewrite H2; apply DistSym.
	 rewrite DistSym; rewrite H; apply DistSym.
Qed.

Lemma CongruentTrianglesACB : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	CongruentTriangles A C B A' C' B'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
	 rewrite DistSym; rewrite H2; apply DistSym.
	 rewrite DistSym; rewrite H; apply DistSym.
	 rewrite DistSym; rewrite H0; apply DistSym.
Qed.

Lemma CongruentTrianglesCBA : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	CongruentTriangles C B A C' B' A'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
	 rewrite DistSym; rewrite H; apply DistSym.
	 rewrite DistSym; rewrite H0; apply DistSym.
	 rewrite DistSym; rewrite H2; apply DistSym.
Qed.

Lemma CongruentTrianglesBCA : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	CongruentTriangles B C A B' C' A'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
Qed.

Lemma CongruentTrianglesCAB : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	CongruentTriangles C A B C' A' B'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
Qed.

Lemma CongruentTrianglesAB : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	Distance A B = Distance A' B'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
Qed.

Lemma CongruentTrianglesBC : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	Distance B C = Distance B' C'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
Qed.

Lemma CongruentTrianglesCA : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	Distance C A = Distance C' A'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
Qed.

Lemma CongruentTrianglesA : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	A <> B ->
	A <> C ->
	Angle B A C = Angle B' A' C'.
Proof.
	unfold CongruentTriangles in |- *; intros.
	apply CongruentSSS; intuition.
	rewrite (DistSym A C); rewrite (DistSym A' C'); trivial.
Qed.

Lemma CongruentTrianglesB : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	B <> A ->
	B <> C ->
	Angle A B C = Angle A' B' C'.
Proof.
	unfold CongruentTriangles in |- *; intros.
	apply CongruentSSS; intuition.
	 rewrite DistSym; rewrite H2; apply DistSym.
	 rewrite DistSym; rewrite H4; apply DistSym.
Qed.

Lemma CongruentTrianglesC : forall A B C A' B' C' : Point,
	CongruentTriangles A B C A' B' C' ->
	C <> A ->
	C <> B ->
	Angle A C B = Angle A' C' B'.
Proof.
	unfold CongruentTriangles in |- *; intros.
	apply CongruentSSS; intuition.
	rewrite DistSym; rewrite H; apply DistSym.
Qed.

Lemma CongruentTrianglesSASA : forall A B C A' B' C' : Point,
	Distance A B = Distance A' B' ->
	Distance A C = Distance  A' C' ->
	Angle B A C = Angle B' A'  C' ->
	A <> B ->
	A <> C ->
	CongruentTriangles A B C A' B' C'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
	 apply (CongruentSAS A B C A' B' C'); intuition.
	 rewrite DistSym; rewrite H0; apply DistSym.
Qed.

Lemma CongruentTrianglesSASB : forall A B C A' B' C' : Point,
	Distance B A = Distance B' A' ->
	Distance B C = Distance  B' C' ->
	Angle A B C = Angle A' B' C' ->
	B <> A ->
	B <> C ->
	CongruentTriangles A B C A' B' C'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
	 rewrite DistSym; rewrite H; apply DistSym.
	 rewrite (DistSym C A); rewrite (DistSym C' A').
	   apply (CongruentSAS B A C B' A' C'); intuition.
Qed.

Lemma CongruentTrianglesSASC : forall A B C A' B' C' : Point,
	Distance C A = Distance C' A'  ->
	Distance C B = Distance  C' B'  ->
	Angle A C B = Angle A' C' B' ->
	C <> A ->
	C <> B ->
	CongruentTriangles A B C A' B' C'.
Proof.
	unfold CongruentTriangles in |- *; intuition.
	 apply (CongruentSAS C A B C' A' B'); intuition.
	 rewrite DistSym; rewrite H0; apply DistSym.
Qed.

End CONGRUENT_TRIANGLES.
