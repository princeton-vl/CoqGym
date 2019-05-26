Require Export B2_Orient_Prop.

Section COLLINEAR_PROPERTIES.

Lemma CollinearAAB : forall A B, Collinear A A B.
Proof.
	split; apply NotClockwiseAAB.
Qed.

Lemma CollinearABA : forall A B, Collinear A B A.
Proof.
	split.
	 apply NotClockwiseABA.
	 apply NotClockwiseBAA.
Qed.

Lemma CollinearABB : forall A B, Collinear A B B.
Proof.
	split.
	 apply NotClockwiseBAA.
	 apply NotClockwiseABA.
Qed.

Lemma NotCollinearDistinctAB : forall A B C : Point,
	~Collinear A B C ->
	A <> B.
Proof.
	canonize.
	subst; elim H1; apply NotClockwiseAAB.
Qed.

Lemma NotCollinearDistinctCA : forall A B C : Point,
	~Collinear A B C ->
	C <> A.
Proof.
	canonize.
	subst; elim H1.
	 apply NotClockwiseABA.
	 apply NotClockwiseBAA.
Qed.

Lemma NotCollinearDistinctBC : forall A B C : Point,
	~Collinear A B C ->
	B <> C.
Proof.
	canonize.
	subst; elim H1.
	 apply NotClockwiseBAA.
	 apply NotClockwiseABA.
Qed.

Lemma CollinearBCA : forall A B C,
	Collinear A B C -> Collinear B C A.
Proof.
	unfold Collinear in |- *; intros.
	decompose [and] H; split.
	 intro; elim H0.
	   apply ClockwiseCAB; trivial.
	 intro; elim H1.
	   apply ClockwiseBCA; trivial.
Qed.

Lemma CollinearCAB : forall A B C,
	Collinear A B C -> Collinear C A B.
Proof.
	intros; do 2 apply CollinearBCA; trivial.
Qed.

Lemma CollinearBAC : forall A B C,
	Collinear A B C -> Collinear B A C.
Proof.
	unfold Collinear in |- *; intuition.
Qed.

Lemma CollinearACB : forall A B C,
	Collinear A B C -> Collinear A C B.
Proof.
	intros; apply CollinearBAC; apply CollinearCAB; trivial.
Qed.

Lemma CollinearCBA : forall A B C,
	Collinear A B C -> Collinear C B A.
Proof.
	intros; apply CollinearBAC; apply CollinearBCA; trivial.
Qed.

Lemma CollinearNotClockwiseABC : forall A B C,
	Collinear A B C -> ~Clockwise A B C.
Proof.
	intros A B C H; destruct H; intuition.
Qed.

Lemma CollinearNotClockwiseBAC : forall A B C,
	Collinear A B C -> ~Clockwise B A C.
Proof.
	intros A B C H; destruct H; intuition.
Qed.

Lemma ClockwiseNotCollinear : forall A B C,
	Clockwise A B C ->
	~Collinear A B C.
Proof.
	unfold Collinear in |- *; intuition.
Qed.

Lemma CollinearClockwiseDistinct : forall A B C D,
	Collinear A B C ->
	Clockwise A B D ->
	C <> D.
Proof.
	intros A B C D H H0 H1; subst.
	elim (ClockwiseNotCollinear A B D H0); trivial.
Qed.

End COLLINEAR_PROPERTIES.
