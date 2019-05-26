Require Export B8_Point_Def.

Section TRIANGLE_SPECIFICATION.

Lemma TriangleSpecPerm : forall A B C : Point,
	TriangleSpec (Distance A B) (Distance B C) (Distance C A) ->
	TriangleSpec (Distance B C) (Distance C A) (Distance A B) .
Proof.
	unfold TriangleSpec in |- *; intuition.
Qed.

Lemma ClockwiseTriangleSpec : forall A B C : Point,
	Clockwise A B C ->
	TriangleSpec (Distance A B) (Distance B C) (Distance C A).
Proof.
	unfold TriangleSpec in |- *; intuition.
	 rewrite (DistSym A B); apply TriangularIneq.
	   apply ClockwiseBCA; auto.
	 rewrite (DistSym B C); apply TriangularIneq.
	   apply ClockwiseCAB; auto.
	 rewrite (DistSym C A); apply TriangularIneq; auto.
Qed.

End TRIANGLE_SPECIFICATION.
