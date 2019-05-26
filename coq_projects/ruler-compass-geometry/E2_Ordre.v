Require Export E1_Incidence.

Section ORDERING.

(* B1 : If B is between A and C, then A, B, C are distinct points on a line, and also B is between C and A. *)

Lemma B1a : forall A B C,
	Between A B C -> A <> B.
Proof.
	exact BetweenDistinctAB.
Qed.

Lemma B1b : forall A B C,
	Between A B C -> B <> C.
Proof.
	exact BetweenDistinctBC.
Qed.

Lemma B1c : forall A B C,
	Between A B C -> C <> A.
Proof.
	exact BetweenDistinctCA.
Qed.

Lemma B1d : forall A B C,
	Between A B C -> Collinear A B C.
Proof.
	intros; apply HalfLineCollinear; apply BetweenHalfLine; trivial.
Qed.

Lemma B1e : forall A B C,
	Between A B C -> Between C B A.
Proof.
	exact BetweenSym.
Qed.

(* B2 : For any two distinct points A, B, there exists a points C such that B is between A and C. *)

Lemma B2 : forall A B,
	A <> B ->
	{C : Point | Between A B C}.
Proof.
	intros.
	destruct (CentralSymetPoint A B H) as (C, (H1, H2)).
	exists C; trivial.
Qed.

(* B3 : Given three distinct points on a line, one and only one of them is between the other two. *)

Lemma B3a : forall A B C,
	A <> B ->
	B <> C -> 
	C <> A ->
	Collinear A B C ->
	Between A B C \/ Between B C A \/ Between C A B.
Proof.
	intros.
	destruct (ExclusiveCollinear A B C); auto.
	destruct (ExclusiveCollinear C B A); auto.
	 autoCollinear.
	 left; apply HalfLineBetween; auto.
	 right; left; apply BetweenSym; auto.
Qed.

Lemma B3b : forall A B C,
	Between A B C ->
	~Between B A C.
Proof.
	intros A B C H; unfold Between in |- *; intuition.
	destruct (ClockwiseExists B A H1) as (D, H3).
	elim (ClockwiseNotClockwise B A D H3).
	apply (HalfLineSym A B C (sym_not_eq H1) (BetweenHalfLine A B C H)).
	apply (H2 D H3).
Qed.

Lemma B3c : forall A B C,
	Between A B C ->
	~Between A C B.
Proof.
	intros A B C H H0.
	elim (B3b B C A (BetweenSym A C B H0)).
	apply BetweenSym; trivial.
Qed.

(* B4 : (Pasch). Let A, B, C be three noncollinear points, and let L be a line not containing any of A, B, C. If L contains a point D lying between A and B, 
then it must contain either a point lying between A and C or a point lying between B and C, but not both. *)

Lemma B4a : forall A B C M N,
	~Collinear A B C ->
	Between A M B ->
	~Collinear A M N ->
	~Collinear B M N ->
	~Collinear C M N ->
	(exists P : Point, Collinear M N P /\ Between A P C) \/
	(exists P : Point, Collinear M N P /\ Between B P C).
Proof.
	intros; decompose [or] (ThreeCases A B C).
	 apply PaschABC; auto.
	 assert
	  ((exists P : Point, Collinear M N P /\ Between B P C) \/
	   (exists P : Point, Collinear M N P /\ Between A P C)).
	  apply PaschABC; auto.
	    apply BetweenSym; trivial.
	  tauto.
	 canonize.
Qed.

Lemma B4b : forall A B C M N P Q,
	~Collinear A B C ->
	Between A M B ->
	~Collinear A M N ->
	~Collinear B M N ->
	~Collinear C M N ->
	Collinear M N P ->
	Between A P C ->
	Collinear M N Q -> 
	Between B Q C ->
	False.
Proof.
	intros.
	destruct (B3a M P Q).
	 exact (NotCollinearBetweenDistinct A B C M P H H0 H5).
	 apply (NotCollinearBetweenDistinct C A B P Q).
	  intro; elim H; autoCollinear.
	  apply BetweenSym; auto.
	  apply BetweenSym; auto.
	 apply (NotCollinearBetweenDistinct B C A Q M).
	  intro; elim H; autoCollinear.
	  trivial.
	  apply BetweenSym; auto.
	 apply (CollinearTrans M N P Q (NotCollinearDistinctBC A M N H1) H4 H6).
	 elim H; clear H H1 H2 H3.
	   split; intro.
	  apply (NotFourBetween A B C M P Q); auto.
	    apply (ClockwiseBetweenClockwise A B C M P); auto.
	  apply (NotFourBetween C B A Q P M).
	   apply (ClockwiseBetweenClockwise C B A Q P).
	    autoClockwise.
	    apply BetweenSym; trivial.
	    apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	 elim H; clear H H1 H2 H3.
	   split; intro; destruct H8.
	  apply (NotFourBetween C A B P Q M).
	   apply (ClockwiseBetweenClockwise C A B P Q).
	    autoClockwise.
	    apply BetweenSym; trivial.
	    apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	   trivial.
	   trivial.
	  apply (NotFourBetween B C A Q M P).
	   apply (ClockwiseBetweenClockwise B C A Q M).
	    autoClockwise.
	    trivial.
	    apply BetweenSym; trivial.
	   trivial.
	   apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
	   trivial.
	  apply (NotFourBetween B A C M Q P).
	   apply (ClockwiseBetweenClockwise B A C M Q).
	    trivial.
	    apply BetweenSym; trivial.
	    trivial.
	   apply BetweenSym; trivial.
	   trivial.
	   trivial.
	   apply BetweenSym; trivial.
	  apply (NotFourBetween A C B P M Q).
	   apply (ClockwiseBetweenClockwise A C B P M).
	    autoClockwise.
	    trivial.
	    trivial.
	   trivial.
	   trivial.
	   apply BetweenSym; trivial.
	   apply BetweenSym; trivial.
Qed.

End ORDERING.
