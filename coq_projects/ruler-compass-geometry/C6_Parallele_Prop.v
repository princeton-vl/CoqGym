Require Export C5_Droite_Prop.

Section EQUIDIRECTED_PROPERTIES.

Lemma EquiDirectedRefl : forall A B : Point,
EquiDirected A B A B.
Proof.
	canonize.
Qed.

Lemma EquiDirectedSym : forall A B C D : Point,
EquiDirected A B C D ->
EquiDirected C D A B.
Proof.
	canonize.
Qed.

Lemma EquiDirectedPermut : forall A B C D : Point,
EquiDirected A B C D ->
EquiDirected B A C D.
Proof.
	canonize.
Qed.

Lemma EquiDirectedPermutCD: forall A B C D : Point, 
	EquiDirected A B C D -> 
	EquiDirected A B D C.
Proof.
	intros; apply EquiDirectedSym; apply EquiDirectedPermut;
	 apply EquiDirectedSym; trivial.
Qed.

Lemma  ParallelNotClockwiseABC : forall A B C D,
	EquiOriented A B C D ->
	~Clockwise A B C.
Proof.
	canonize.
	elim (NotClockwiseABA C D); auto.
Qed.

Lemma  ParallelNotClockwiseABD : forall A B C D,
	EquiOriented A B C D ->
	~Clockwise A B D.
Proof.
	canonize.
	elim (NotClockwiseBAA D C); auto.
Qed.

Lemma  ParallelCollinearABD : forall A B C D,
	EquiOriented A B C D ->
	Collinear A B C ->
	Collinear A B D.
Proof.
	canonize.
	 elim (NotClockwiseBAA D C); auto.
	 destruct (CollinearHalfLine A B C).
	  canonize.
	  generalizeChange.
	    elim (NotClockwiseBAA A B); apply H3.
	   autoDistinct.
	   assert (Clockwise C A D); [ auto | autoClockwise ].
	  generalizeChange.
	    elim (HalfLineNotClockwiseBAC C B D).
	   canonize.
	     apply H; apply H5.
	    autoDistinct.
	    trivial.
	   canonize.
Qed.

Lemma  ParallelCollinearABC : forall A B C D,
	EquiOriented A B C D ->
	Collinear A B D ->
	Collinear A B C.
Proof.
	canonize.
	 elim (NotClockwiseABA C D); auto.
	 destruct (CollinearHalfLine A B D).
	  canonize.
	  generalizeChange.
	    elim (HalfLineNotClockwiseBAC D C A).
	   canonize.
	     apply H6; apply H3.
	    autoDistinct.
	    trivial.
	   assert (Clockwise D A C).
	    auto.
	    autoClockwise.
	  generalizeChangeSide.
	    elim (NotClockwiseABA B A); apply H3.
	   autoDistinct.
	   assert (Clockwise B D C).
	    auto.
	    autoClockwise.
Qed.

Lemma  ParallelCollinearCDB : forall A B C D,
	EquiOriented A B C D ->
	Collinear C D A ->
	Collinear C D B.
Proof.
	canonize.
	 destruct (CollinearHalfLine C D A).
	  canonize.
	  elim (NotClockwiseABA C D); apply H.
	    generalize (H3 B H0); intro; autoClockwise.
	  elim (HalfLineNotClockwiseBAC A B D).
	   generalizeChange.
	   assert (Clockwise A D B).
	    generalizeChange.
	    autoClockwise.
	 elim (NotClockwiseABA B A).
	   generalizeChange.
	   apply H3.
	  apply (CollinearClockwiseDistinct D C A B).
	   canonize.
	   auto.
	  auto.
Qed.

Lemma  ParallelCollinearCDA : forall A B C D,
	EquiOriented A B C D ->
	Collinear C D B ->
	Collinear C D A.
Proof.
	canonize.
	 destruct (CollinearHalfLine C D B).
	  canonize.
	  elim (HalfLineNotClockwiseBAC B C A).
	   generalizeChange.
	     apply H3.
	    intro; destruct (CollinearClockwiseDistinct C D B A); canonize.
	    apply H6.
	     autoDistinct.
	     trivial.
	   generalizeChange.
	  elim (NotClockwiseBAA D C); apply H.
	    assert (Clockwise B D A).
	   generalizeChange.
	   autoClockwise.
	 generalizeChangeSide.
	   elim (NotClockwiseBAA A B); apply H3.
	  intro; destruct (CollinearClockwiseDistinct D C B A); canonize.
	  trivial.
Qed.

End EQUIDIRECTED_PROPERTIES.

