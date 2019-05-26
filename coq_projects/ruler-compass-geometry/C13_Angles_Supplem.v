Require Export C12_Angles_Opposes.

Section SUPPLEMENTARY_ANGLES.

Definition Supplementary (alpha beta : AS) :=
exists A  : Point,  exists B  : Point,  exists C : Point,  exists D : Point, 
	A <> C /\ Between B A D /\ Angle B A C = alpha /\ Angle C A D = beta.

Lemma SupplementaryCommut : forall alpha beta : AS,
	Supplementary alpha beta ->
	Supplementary beta alpha.
Proof.
	unfold Supplementary in |- *;
	 intros alpha beta (A, (B, (C, (D, (H0, (H1, (H2, H3))))))).
	exists A; exists D; exists C; exists B; intuition.
	 apply BetweenSym; trivial.
	 rewrite AngleSym.
	  trivial.
	  apply (BetweenDistinctBC _ _ _ H1).
	  trivial.
	 rewrite AngleSym.
	  trivial.
	  trivial.
	  apply (sym_not_eq (BetweenDistinctAB _ _ _ H1)).
Qed.
 
Lemma HalfLineBetweenBetween : forall A B C D : Point,
       	Between A C D -> 
	HalfLine C A B -> 
	Between B C D.
Proof.
	intros.
	apply BetweenSym; apply (BetweenHalfLineBetween D C A B).
	 apply BetweenSym; trivial.
	 trivial.
Qed.

Lemma SupplementBC : forall A B C D A' B' C' D' : Point,
	A <> C ->
	A' <> C' ->
	B <> C ->
	Between B A D ->
	Between B' A' D' ->
	Angle B A C = Angle B' A' C' ->
	Angle C A D = Angle C' A' D'.
Proof.
	intros A B C D A' B' C' D' dAC dA'C' dBC H0 H1 H2.
	assert (dAB := sym_not_eq (BetweenDistinctAB _ _ _ H0)).	
	assert (dA'B' := sym_not_eq (BetweenDistinctAB _ _ _ H1)).
	destruct (ExistsHalfLineEquidistant A' B' A B dA'B' dAB) as (B'', (H3, H4)).
	destruct (ExistsHalfLineEquidistant A' C' A C dA'C' dAC) as (C'', (H5, H6)).
	assert (dAD := BetweenDistinctBC _ _ _ H0).	
	assert (dA'D' := BetweenDistinctBC _ _ _ H1).
	destruct (ExistsHalfLineEquidistant A' D' A D dA'D' dAD) as (D'', (H7, H8)).
	rewrite (HalfLineAngleBC A' C' D' C'' D'' dA'C' dA'D' H5 H7).
	apply (CongruentSSS A C D A' C'' D'' dAC dAD (sym_eq H6) (sym_eq H8)).
	assert (dBD := sym_not_eq (BetweenDistinctCA _ _ _ H0)).
	assert (H9 : Distance B C = Distance B'' C'').
	 apply (CongruentSAS A B C A' B'' C'' dAB dAC (sym_eq H4) (sym_eq H6)).
	   rewrite H2; apply (HalfLineAngleBC A' B' C' B'' C'' dA'B' dA'C' H3 H5).
	 assert (H10 : Distance B D = Distance B'' D'').
	  rewrite <- (ChaslesBetween B A D H0).
	    rewrite (DistSym B A); rewrite <- H4.
	    rewrite <- H8; rewrite (DistSym A' B'').
	    apply ChaslesBetween.
	    apply (BetweenHalfLineBetween B'' A' D' D'').
	   apply (HalfLineBetweenBetween B'); trivial.
	   trivial.
	  apply (CongruentSAS B C D B'' C'' D'' dBC dBD H9 H10).
	    rewrite (HalfLineAngleC B C D A dBC dBD).
	   rewrite (HalfLineAngleC B'' C'' D'' A').
	    apply (CongruentSSS B C A B'' C'' A' dBC (sym_not_eq dAB) H9).
	     autoDistance.
	     autoDistance.
	    apply (EquiDistantDistinct B C B'' C'' dBC H9).
	    apply (EquiDistantDistinct B D B'' D'' dBD H10).
	    apply
	     (HalfLineSym B'' A' D''
	        (sym_not_eq (EquiDistantDistinct A B A' B'' dAB (sym_eq H4)))).
	      apply BetweenHalfLine.
	      apply (BetweenHalfLineBetween B'' A' D' D'').
	     apply (HalfLineBetweenBetween B'); trivial.
	     trivial.
	   apply (HalfLineSym B A D (sym_not_eq dAB)).
	     apply BetweenHalfLine; auto.
 Qed.

Lemma Supplement : forall A B C D A' B' C' D' : Point,
	A <> C ->
	A' <> C' ->
	Between B A D ->
	Between B' A' D' ->
	Angle B A C = Angle B' A' C' ->
	Angle C A D = Angle C' A' D'.
Proof.
	intros A B C D A' B' C' D' dAC dA'C' H0 H1 H2.
	assert (dAB := sym_not_eq (BetweenDistinctAB _ _ _ H0)).
	destruct (CentralSymetPoint A B dAB) as (B'', (H3, H4)).
	assert (dBB'' := BetweenDistinctBC A B B'' H4).
	destruct (Apart B B'' C dBB'').
	 apply (SupplementBC A B C D A' B' C' D' dAC dA'C' H H0 H1 H2).
	 apply (SupplementBC A B'' C D A' B' C' D' dAC dA'C' H).
	  apply (BetweenAssocRight B'' B A D (BetweenSym A B B'' H4) H0).
	  exact H1.
	  rewrite <- (HalfLineAngleB A B C B'' dAB dAC).
	   exact H2.
	   apply BetweenHalfLine; auto.
Qed.

Lemma SupplementaryEq : forall alpha beta gamma : AS,
	Supplementary alpha beta ->
	Supplementary alpha gamma ->
	beta = gamma.
Proof.
	unfold Supplementary in |- *;
	 intros alpha beta gamma (A, (B, (C, (D, (H0, (H1, (H2, H3)))))))
	  (A', (B', (C', (D', (H4, (H5, (H6, H7))))))).
	rewrite <- H3; rewrite <- H7.
	apply (Supplement A B C D A' B' C' D' H0 H4 H1 H5).
	subst; auto.
Qed.

Lemma OpposedAtVertex : forall A B C D E : Point,
	Between B A D ->
	Between C A E ->
	Angle B A C = Angle D A E.
Proof.
	intros.
	assert (dAB := sym_not_eq (BetweenDistinctAB _ _ _ H)).
	assert (dAC := sym_not_eq (BetweenDistinctAB _ _ _ H0)).
	rewrite (AngleSym A B C dAB dAC).
	assert (dAD := BetweenDistinctBC _ _ _ H).
	apply (Supplement A D C B A C D E dAC dAD).
	 apply BetweenSym; auto.
	 trivial.
	 apply AngleSym; auto.
Qed.

Lemma CongruentOpposedTriangles : forall A B C D I : Point,
	Between A I C ->
	Between B I D ->
	Distance I A = Distance I C ->
	Distance I B = Distance I D ->
	CongruentTriangles A I B C I D.
Proof.
	intros.
	apply CongruentTrianglesSASB.
	 trivial.
	 trivial.
	 apply OpposedAtVertex; trivial.
	 apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H).
	 apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H0).
Qed.

Lemma SupplementaryRec : forall A B C D : Point,
	Clockwise B A C ->
	Clockwise C A D ->
	Supplementary (Angle B A C) (Angle C A D) ->
	Between B A D.
Proof.
	intros.
	destruct H1 as (A', (B', (C', (D', (H1, (H2, (H3, H4))))))).
	destruct (ExistsHalfLineEquidistant A B A' B') as (B'', (H5, H6)).
	 autoDistinct.
	 apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H2).
	 destruct (ExistsHalfLineEquidistant A C A' C') as (C'', (H7, H8)).
	  autoDistinct.
	  trivial.
	  destruct (ExistsHalfLineEquidistant A D A' D') as (D'', (H9, H10)).
	   autoDistinct.
	   apply (BetweenDistinctBC _ _ _ H2).
	   destruct (ExistsBetweenEquidistant A B A' D') as (E, (H11, H12)).
	    autoDistinct.
	    apply (BetweenDistinctBC _ _ _ H2).
	    assert (CongruentStrictTriangles B'' A C'' B' A' C').
	     apply CongruentStrictTrianglesSASB.
	      trivial.
	      trivial.
	      rewrite H3; apply sym_eq; apply HalfLineAngleBC.
	       autoDistinct.
	       autoDistinct.
	       trivial.
	       trivial.
	      intro; elim (ClockwiseNotCollinear _ _ _ H).
	        apply CollinearBAC; apply (CollinearTrans A B'' B C).
	       apply (EquiDistantDistinct A' B' A B'').
	        apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H2).
	        autoDistance.
	       apply CollinearACB; apply (HalfLineCollinear _ _ _ H5).
	       apply CollinearACB; apply (CollinearTrans A C'').
	        apply (EquiDistantDistinct A' C' A C''); auto.
	        apply CollinearACB; apply (HalfLineCollinear _ _ _ H7).
	        autoCollinear.
	     assert (CongruentStrictTriangles B'' E C'' B' D' C').
	      apply CongruentStrictTrianglesSASA.
	       rewrite <- (ChaslesBetween B'' A E).
	        rewrite (DistSym B'' A); rewrite H12; rewrite H6.
	          rewrite (DistSym A' B'); apply ChaslesBetween; auto.
	        apply BetweenSym; apply (BetweenHalfLineBetween E A B B''); trivial.
	       rewrite (DistSym B'' C''); rewrite (DistSym B' C').
	         apply (CongruentStrictTrianglesCA _ _ _ _ _ _ H13).
	       apply trans_eq with (y := Angle A B'' C'').
	        apply HalfLineAngleB.
	         intro; subst; canonize.
	           destruct (ClockwiseExists E A H2) as (F, H17).
	           elim (ClockwiseNotClockwise _ _ _ H17); auto.
	         intro; subst; elim (ClockwiseNotCollinear _ _ _ H).
	           apply CollinearBAC; apply (CollinearTrans A C'').
	          apply (EquiDistantDistinct A' C' A C''); auto.
	          apply CollinearACB; apply (HalfLineCollinear _ _ _ H5).
	          apply CollinearACB; apply (HalfLineCollinear _ _ _ H7).
	         apply HalfLineSym.
	          apply sym_not_eq; apply (HalfLineDistinct A B B'').
	           autoDistinct.
	           trivial.
	          apply BetweenHalfLine.
	            apply (HalfLineBetweenBetween B).
	           apply BetweenSym; trivial.
	           trivial.
	        apply trans_eq with (y := Angle A' B' C').
	         apply CongruentStrictTrianglesA; trivial.
	         apply HalfLineAngleB.
	          apply (BetweenDistinctAB _ _ _ H2).
	          intro; subst.
	            elim (ClockwiseNotCollinear _ _ _ H).
	            apply CollinearBAC; apply HalfLineCollinear.
	            apply NullAngleHalfLine.
	           autoDistinct.
	           autoDistinct.
	           rewrite <- H3; apply NullAngle.
	            trivial.
	            canonize.
	          apply BetweenHalfLine; trivial.
	       intro; destruct H13.
	         elim H15; apply (CollinearTrans B'' E).
	        intro; subst; canonize.
	          destruct (ClockwiseExists E A H2) as (F, H20).
	          elim (ClockwiseNotClockwise _ _ _ H20); auto.
	        apply CollinearBCA; apply (CollinearTrans A B).
	         autoDistinct.
	         apply (HalfLineCollinear _ _ _ H5).
	         apply CollinearBCA; apply (BetweenCollinear _ _ _ H11).
	        trivial.
	      assert (E = D'').
	       apply (SSSEqualCD C'' A).
	        clear H5 H2 H9; generalizeChange.
	          apply H15; apply ClockwiseCAB; apply H17; trivial.
	        clear H2 H5 H11; generalizeChangeSense.
	          apply H2; apply ClockwiseCAB; apply H9; autoClockwise.
	        apply trans_eq with (y := Distance C' D').
	         apply
	          (CongruentStrictTrianglesBC _ _ _ _ _ _
	             (CongruentStrictTrianglesACB _ _ _ _ _ _ H14)).
	         assert (CongruentStrictTriangles C'' A D'' C' A' D').
	          apply CongruentStrictTrianglesSASB.
	           trivial.
	           trivial.
	           rewrite H4; apply sym_eq; apply HalfLineAngleBC.
	            autoDistinct.
	            autoDistinct.
	            trivial.
	            trivial.
	           intro; elim (ClockwiseNotCollinear _ _ _ H0).
	             apply CollinearBAC; apply (CollinearTrans A C'').
	            apply (EquiDistantDistinct A' C'); auto.
	            apply CollinearACB; apply (HalfLineCollinear _ _ _ H7).
	            apply (CollinearTrans A D'').
	             apply (EquiDistantDistinct A' D').
	              apply (BetweenDistinctBC _ _ _ H2).
	              auto.
	             autoCollinear.
	             apply CollinearACB; apply (HalfLineCollinear _ _ _ H9).
	          apply sym_eq;
	           apply
	            (CongruentStrictTrianglesCA _ _ _ _ _ _
	               (CongruentStrictTrianglesCBA _ _ _ _ _ _ H15)).
	        autoDistance.
	       apply (BetweenHalfLineBetween B A D'').
	        subst; apply (BetweenSym _ _ _ H11).
	        apply HalfLineSym.
	         autoDistinct.
	         trivial.
Qed.

End SUPPLEMENTARY_ANGLES.
