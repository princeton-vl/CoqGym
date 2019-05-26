Require Export B1_Confondu_Prop.

Section CLOCKWISE_PROPERTIES.

Lemma ClockwiseBCA : forall A B C, 
	Clockwise A B C -> Clockwise B C A.
Proof.
	exact ClockwisePerm.
Qed.

Lemma ClockwiseCAB : forall A B C, 
	Clockwise A B C -> Clockwise C A B.
Proof.
	intros A B C H; do 2 apply ClockwisePerm; trivial.
Qed.

Lemma NotClockwiseAAB : forall A B, ~Clockwise A A B.
Proof.
	intros A B; destruct (ClockwiseAntisym A A B); trivial.
Qed.

Lemma NotClockwiseABA : forall A B , ~Clockwise A B A.
Proof.
	intros A B H; elim (NotClockwiseAAB A B); apply ClockwiseCAB; trivial.
Qed.

Lemma NotClockwiseBAA : forall A B , ~Clockwise B A A.
Proof.
	intros A B H; elim (NotClockwiseAAB A B); apply ClockwiseBCA; trivial.
Qed.

Lemma ClockwiseDistinctAB : forall A B C,
	Clockwise A B C -> A <> B.
Proof.
	intros A B C H Hi; subst.
	elim (NotClockwiseAAB B C); trivial.
Qed.

Lemma ClockwiseDistinctBC : forall A B C,
	Clockwise A B C -> B <> C.
Proof.
	intros A B C H Hi; subst.
	elim (NotClockwiseBAA C A); trivial.
Qed.

Lemma ClockwiseDistinctCA : forall A B C,
	Clockwise A B C -> C <> A.
Proof.
	intros A B C H Hi; subst.
	elim (NotClockwiseABA A B); trivial.
Qed.

Lemma ClockwiseNotClockwise : forall A B C,
	Clockwise A B C -> ~Clockwise B A C.
Proof.
	intros A B C H H0.
	destruct (ClockwiseAntisym A B C); intuition.
Qed.

Lemma ClockwiseClockwiseDistinct : forall A B C D,
	Clockwise A B C ->
	Clockwise B A D ->
	C <> D.
Proof.
	intros A B C D H H0 H1; subst.
	elim (ClockwiseNotClockwise A B D H); trivial.
Qed.

Lemma ExclusiveFourCases : forall A B C,
	A <> C ->
	Clockwise A B C \/
	Clockwise B A C \/
	HalfLine A B C \/
	EquiOriented A B C A.
Proof.
	intros A B C H; decompose [or] (FourCases A B C).
	 auto.
	 auto.
	 auto.
	 decompose [or] (FourCases A C B).
	  generalize (ClockwiseCAB A C B H1); auto.
	  generalize (ClockwiseBCA C A B); auto.
	  generalizeChange.
	  generalizeChange.
Qed.
	
End CLOCKWISE_PROPERTIES.
