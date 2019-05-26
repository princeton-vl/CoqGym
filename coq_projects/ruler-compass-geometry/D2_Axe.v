Require Export D1_DistanceProp.

Section AXIS.

Require Export Arith.

Variables A B : Point.

Hypothesis Hab : A <> B.

Definition StrongGraduation : forall n : nat,
	{N : Point | HalfLine A N B /\ Distance A N = DistTimesn n A B /\ (n > 0 -> A <> N)}.
Proof.
	intro n.
	 case n.
	  exists A; repeat split.
	   canonize.
	     elim (NotClockwiseAAB A x H).
	   intro H; inversion H.
	  induction n0.
	   exists B; repeat split.
	    canonize.
	    simpl in |- *.
	      rewrite NullDist; rewrite LS0NeutralRight; trivial.
	    intuition.
	   destruct IHn0 as (N, (H1, (H2, H3))).
	     assert (H : A <> N).
	    intuition.
	    destruct (ExistsBetweenEquidistant N A A B) as (P, (H4, H5)).
	     auto.
	     trivial.
	     exists P; repeat split.
	      assert (H6 := BetweenSymHalfLine _ _ _ H4).
	        assert (H7 := HalfLineSym A N P H H6).
	        canonize.
	      change
	        (DistTimesn (S (S n0)) A B) with (LSplus (Distance A B)
	                                            (DistTimesn (S n0) A B)) in |- *.
	        rewrite <- H2; rewrite <- H5; rewrite LSplusComm.
	       rewrite ChaslesBetween.
	        trivial.
	        apply BetweenSym; trivial.
	       apply (EquiDistantDistinct A B); trivial.
	         autoDistance.
	       trivial.
	      intros _; exact (BetweenDistinctCA _ _ _ H4).
Defined.

Definition Graduation : forall n : nat,
	{N : Point | HalfLine A N B /\ Distance A N = DistTimesn n A B}.
Proof.
	intro n; destruct (StrongGraduation n) as (P, H0); exists P; intuition.
Defined.

End AXIS.
