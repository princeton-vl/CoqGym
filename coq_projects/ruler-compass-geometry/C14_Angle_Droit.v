Require Export C13_Angles_Supplem.

Unset Standard Proposition Elimination Names.

Section RIGHTANGLE.

Definition Vv : Point.
Proof.
	destruct (EquilateralClockwise Uu Ww (BetweenDistinctCA Ww Oo Uu BetweenWwOoUu))
	 as (X, (H1,H2)).
	destruct (ExistsHalfLineEquidistant Oo X Oo Uu) as (Y, (H3, H4)).
	 intro; subst.
	   elim (ClockwiseNotCollinear _ _ _ H2).
	   apply CollinearACB; exact (BetweenCollinear _ _ _ BetweenUuOoWw).
	 exact DistinctOoUu.
	 exact Y.
Defined.

Lemma DistOoVv : Distance Oo Vv = Distance Oo Uu.
Proof.
	unfold Vv in |- *.
	destruct
	 (EquilateralClockwise Uu Ww (BetweenDistinctCA Ww Oo Uu BetweenWwOoUu)).
	case a; simpl in |- *; intros.
	destruct
	 (ExistsHalfLineEquidistant Oo x Oo Uu
	    (fun H : Oo = x =>
	     eq_ind Oo
	       (fun X : Point => Equilateral Uu Ww X -> Clockwise Uu Ww X -> False)
	       (fun (_ : Equilateral Uu Ww Oo) (H2 : Clockwise Uu Ww Oo) =>
	        False_ind False
	          (ClockwiseNotCollinear Uu Ww Oo H2
	             (CollinearACB Uu Oo Ww (BetweenCollinear Uu Oo Ww BetweenUuOoWw))))
	       x H e c) DistinctOoUu).
	case a0; simpl in |- *; intros.
	autoDistance.
Qed.

Lemma DistinctOoVv : Oo <> Vv.
Proof.
	apply (EquiDistantDistinct Oo Uu Oo Vv DistinctOoUu).
	apply sym_eq; exact DistOoVv.
Qed.

Lemma ClockwiseUuOoVv : Clockwise Uu Oo Vv.
Proof.
	unfold Vv in |- *.
	destruct
	 (EquilateralClockwise Uu Ww (BetweenDistinctCA Ww Oo Uu BetweenWwOoUu)).
	case a; simpl in |- *; intros.
	destruct
	 (ExistsHalfLineEquidistant Oo x Oo Uu
	    (fun H : Oo = x =>
	     eq_ind Oo
	       (fun X : Point => Equilateral Uu Ww X -> Clockwise Uu Ww X -> False)
	       (fun (_ : Equilateral Uu Ww Oo) (H2 : Clockwise Uu Ww Oo) =>
	        False_ind False
	          (ClockwiseNotCollinear Uu Ww Oo H2
	             (CollinearACB Uu Oo Ww (BetweenCollinear Uu Oo Ww BetweenUuOoWw))))
	       x H e c) DistinctOoUu).
	case a0; simpl in |- *; intros.
	apply ClockwiseCAB; apply h; unfold HalfPlane, In in |- *.
	apply ClockwiseBCA; apply (BetweenClockwiseAMC Uu Ww x Oo c BetweenUuOoWw).
Qed.

Lemma AngleUuOoVv : Angle Uu Oo Vv = Angle Ww Oo Vv.
Proof.
	unfold Vv in |- *.
	destruct
	 (EquilateralClockwise Uu Ww (BetweenDistinctCA Ww Oo Uu BetweenWwOoUu)).
	case a; simpl in |- *; intros.
	destruct
	 (ExistsHalfLineEquidistant Oo x Oo Uu
	    (fun H : Oo = x =>
	     eq_ind Oo
	       (fun X : Point => Equilateral Uu Ww X -> Clockwise Uu Ww X -> False)
	       (fun (_ : Equilateral Uu Ww Oo) (H2 : Clockwise Uu Ww Oo) =>
	        False_ind False
	          (ClockwiseNotCollinear Uu Ww Oo H2
	             (CollinearACB Uu Oo Ww (BetweenCollinear Uu Oo Ww BetweenUuOoWw))))
	       x H e c) DistinctOoUu).
	case a0; simpl in |- *; intros.
	assert (Oo <> x).
	 intro; subst.
	   elim (ClockwiseNotCollinear _ _ _ c).
	   apply CollinearACB; exact (BetweenCollinear _ _ _ BetweenUuOoWw).
	 rewrite <- (HalfLineAngleC Oo Uu x x0 DistinctOoUu H h).
	   rewrite <- (HalfLineAngleC Oo Ww x x0 DistinctOoWw H h).
	   apply CongruentSSS.
	  exact DistinctOoUu.
	  exact H.
	  rewrite DistSym; exact DistOoWw.
	  destruct e; autoDistance.
	  destruct e; autoDistance.
Qed.

Lemma DistVvUu : Distance Vv Uu = Distance Vv Ww.
Proof.
	apply (CongruentSAS Oo Vv Uu Oo Vv Ww).
	 exact DistinctOoVv.
	 exact DistinctOoUu.
	 trivial.
	 rewrite DistSym; exact DistOoWw.
	 rewrite (AngleSym Oo Vv Uu DistinctOoVv DistinctOoUu).
	   rewrite (AngleSym Oo Vv Ww DistinctOoVv DistinctOoWw).
	   exact AngleUuOoVv.
Qed.

Definition RightAS := Angle Uu Oo Vv.

Lemma DoubleRight : Supplementary RightAS RightAS.
Proof.
	unfold Supplementary, RightAS in |- *.
	exists Oo; exists Uu; exists Vv; exists Ww; split.
	 exact DistinctOoVv.
	 split.
	  exact BetweenUuOoWw.
	  split.
	   trivial.
	   rewrite (AngleSym Oo Vv Ww DistinctOoVv DistinctOoWw).
	     apply sym_eq; exact AngleUuOoVv.
Qed.

End RIGHTANGLE.
