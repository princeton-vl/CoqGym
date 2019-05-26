(****************************************************************************
                                                                             
          IEEE754  :  Closest2Prop                                                   
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export ClosestProp.
Section F2.
Variable b : Fbound.
Variable precision : nat.
 
Let radix := 2%Z.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
 
Theorem TwoMoreThanOne : (1 < radix)%Z.
unfold radix in |- *; red in |- *; simpl in |- *; auto.
Qed.
Hint Resolve TwoMoreThanOne.
Hypothesis precisionNotZero : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem FevenNormMin : Even (nNormMin 2%nat precision).
unfold nNormMin in |- *.
generalize precisionNotZero; case precision.
intros H'2; Contradict H'2; auto with zarith.
intros n; case n.
intros H'2; Contradict H'2; auto with zarith.
intros n0 H'2; replace (pred (S (S n0))) with (S n0).
apply EvenExp; auto.
exists 1%Z; ring.
simpl in |- *; auto.
Qed.
 
Theorem EvenFNSuccFNSuccMid :
 forall p : float,
 Fbounded b p ->
 FNeven b radix precision p ->
 Fminus radix (FNSucc b radix precision (FNSucc b radix precision p))
   (FNSucc b radix precision p) = Fminus radix (FNSucc b radix precision p) p
 :>R.
intros p H' H'0.
unfold FtoRradix in |- *; apply FNSuccFNSuccMid; auto.
red in |- *; intros H'1;
 absurd (FNodd b radix precision (FNSucc b radix precision p)); 
 auto.
unfold FNodd in |- *.
rewrite FcanonicFnormalizeEq; auto with float arith.
unfold Fodd in |- *.
rewrite H'1.
apply EvenNOdd; auto with float arith.
apply FevenNormMin; auto with float arith.
apply FNevenSuc; auto.
red in |- *; intros H'1;
 absurd (FNodd b radix precision (FNSucc b radix precision p));
 auto with float arith.
unfold FNodd in |- *.
rewrite FcanonicFnormalizeEq; auto with float arith.
unfold Fodd in |- *.
rewrite H'1.
apply EvenNOdd.
apply EvenOpp; apply FevenNormMin.
Qed.
 
Theorem AScal2 :
 forall p : float, Float (Fnum p) (Fexp p + 1%nat) = (radix * p)%R :>R.
intros p.
unfold FtoRradix in |- *; rewrite FvalScale; auto.
replace (powerRZ radix 1%nat) with (INR 2); [ idtac | simpl in |- *; unfold radix; ring ];
 auto.
Qed.
End F2.
Hint Resolve FevenNormMin: float.