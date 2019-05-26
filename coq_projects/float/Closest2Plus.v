(****************************************************************************
                                                                             
          IEEE754  :  Closest2Plus                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export ClosestPlus.
Require Export Closest2Prop.
Section F2.
Variable b : Fbound.
Variable precision : nat.
 
Let radix := 2%Z.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.
 
Theorem TwoMoreThanOne : (1 < radix)%Z.
red in |- *; simpl in |- *; auto.
Qed.
Hint Resolve TwoMoreThanOne.
Hypothesis precisionNotZero : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem plusUpperBound :
 forall P,
 RoundedModeP b 2%nat P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 Fbounded b p ->
 Fbounded b q -> (Rabs pq <= radix * Rmax (Rabs p) (Rabs q))%R.
intros P H' p q pq H'0 H'1 H'2.
rewrite <- (Rabs_right radix); auto with real zarith.
rewrite <- RmaxRmult; auto with real.
repeat rewrite <- Rabs_mult.
case (Rle_or_lt p q); intros Rltp.
apply RmaxAbs; auto.
apply (RoundedModeMultLess b radix) with (P := P) (r := (p + q)%R); auto.
replace (radix * FtoR radix p)%R with (p + p)%R;
 [ auto with real | unfold radix at 1; fold FtoRradix; ring].
unfold FtoRradix in |- *;
 apply (RoundedModeMult b radix) with (P := P) (r := (p + q)%R); 
 auto.
replace (radix * FtoR radix q)%R with (q + q)%R;
 [ auto with real | unfold radix at 1; fold FtoRradix; ring ].
rewrite RmaxSym.
apply RmaxAbs; auto.
apply (RoundedModeMultLess b radix) with (P := P) (r := (p + q)%R); auto.
replace (radix * FtoR radix q)%R with (q + q)%R;
 [ auto with real | unfold radix at 1; fold FtoRradix; ring ].
unfold FtoRradix in |- *;
 apply (RoundedModeMult b radix) with (P := P) (r := (p + q)%R); 
 auto.
replace (radix * FtoR radix p)%R with (p + p)%R;
 [ auto with real zarith | unfold radix at 1; fold FtoRradix; ring].
Qed.
 
Theorem plusErrorBound2 :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 ~ is_Fzero r ->
 (Rabs (r - (p + q)) < radix * / pPred (vNum b) * Rmax (Rabs p) (Rabs q))%R.
intros p q r H' H'0 H'1 H'2.
apply
 Rlt_le_trans
  with (Rabs (FtoR radix r) * / radix * (radix * / pPred (vNum b)))%R; 
 auto.
unfold FtoRradix in |- *; apply plusErrorBound1 with (precision := precision);
 auto with arith.
replace (Rabs (FtoR radix r) * / radix * (radix * / pPred (vNum b)))%R with
 (radix * / pPred (vNum b) * (Rabs r * / radix))%R; 
 [ idtac | fold FtoRradix; ring ].
apply Rmult_le_compat_l; auto.
replace 0%R with (radix * 0)%R; [ apply Rmult_le_compat_l | ring ].
cut (0 <= radix)%Z; auto with real zarith.
apply Rlt_le; apply Rinv_0_lt_compat; cut (0 < pPred (vNum b))%Z;
 auto with real zarith.
unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *.
apply vNumbMoreThanOne with (radix := radix) (precision := precision);
 auto with real arith.
apply Rmult_le_reg_l with (r := IZR radix); auto with real.
rewrite (Rmult_comm (Rabs r)); rewrite <- Rmult_assoc; rewrite Rinv_r;
 auto with real zarith; rewrite Rmult_1_l.
apply plusUpperBound with (P := Closest b radix); auto.
apply ClosestRoundedModeP with (precision := precision); auto.
Qed.
 
Theorem plusClosestLowerBoundAux1 :
 forall p q pq : float,
 (Rabs q <= p)%R ->
 Closest b radix (p + q) pq ->
 Fbounded b p -> Fbounded b q -> pq <> (p + q)%R :>R -> (/ radix * p <= pq)%R.
intros p q pq H' H'0 H'1 H'2 H'3.
cut (0 <= p)%R;
 [ intros Rl0; Casec Rl0; intros H0
 | apply Rle_trans with (2 := H'); auto with real ].
apply (FmultRadixInv b radix precision) with (5 := H'0); auto.
case (Rle_or_lt 0 q); intros Rl0.
apply Rlt_le_trans with (FtoRradix p); auto.
apply Rlt_RinvDouble; auto.
pattern (FtoRradix p) at 1 in |- *; replace (FtoRradix p) with (p + 0)%R;
 auto with real.
apply Rmult_lt_reg_l with (r := IZR radix); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_l.
apply Rplus_lt_reg_l with (r := (- (radix * p))%R).
replace (- (radix * p) + FtoR radix p)%R with (- p)%R;
 [ idtac | unfold radix at 1; unfold FtoRradix; ring].
replace (- (radix * p) + (radix * p + radix * q))%R with (radix * q)%R;
 [ idtac | simpl in |- *; ring ].
rewrite <- (Ropp_involutive (radix * q)); apply Ropp_lt_contravar.
replace (- (radix * q))%R with (radix * - q)%R; [ idtac | ring ].
case (Rle_or_lt (FtoRradix p) (radix * - q)); auto.
intros H'4; Contradict H'3.
rewrite <- (Fplus_correct radix); auto.
unfold FtoRradix in |- *; apply sym_eq; apply ClosestIdem with (b := b); auto.
replace (Fplus radix p q) with (Fminus radix p (Fopp q)).
rewrite <- Fopp_Fminus.
apply oppBounded; auto.
apply Sterbenz; auto.
apply oppBounded; auto.
apply Rmult_le_reg_l with (r := IZR radix); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r.
rewrite Rmult_1_l; rewrite Fopp_correct; auto.
replace 0%R with (INR 0); auto with real arith.
apply Rle_trans with (FtoR 2%nat p); auto with real.
rewrite Fopp_correct; auto.
rewrite <- Faux.Rabsolu_left1; auto.
apply Rlt_le; auto.
unfold Fminus in |- *; rewrite Fopp_Fopp; auto.
apply
 (ClosestCompatible b radix (p + q)%R (FtoR radix (Fplus radix p q)) pq pq);
 auto.
apply sym_eq; unfold FtoRradix in |- *; apply Fplus_correct; auto.
apply
 RoundedModeBounded
  with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
replace 0%R with (INR 0); auto with real arith.
rewrite <- H0; rewrite Rmult_0_r.
replace (FtoRradix pq) with (FtoRradix p); auto.
rewrite <- H0; auto with real.
unfold FtoRradix in |- *; apply ClosestIdem with (b := b); auto.
apply (ClosestCompatible b radix (p + q)%R (FtoR radix p) pq pq); auto.
replace (FtoR 2%nat p) with (FtoRradix p); auto.
fold FtoRradix; rewrite <- H0; replace (FtoRradix q) with 0%R; try ring.
generalize H'; unfold Rabs in |- *; case (Rcase_abs q); auto.
intros H'4 H'5; Contradict H'5; rewrite <- H0; auto with real.
apply Rlt_not_le; auto with real.
intros H'4 H'5; apply Rle_antisym; auto with real.
rewrite H0; auto.
apply
 RoundedModeBounded
  with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
Qed.
 
Theorem plusClosestLowerBoundAux2 :
 forall p q pq : float,
 Closest b radix (p + q) pq ->
 Fbounded b p ->
 Fbounded b q ->
 pq <> (p + q)%R :>R ->
 (Rabs p <= Rabs q)%R -> (/ radix * Rabs q <= Rabs pq)%R.
intros p q pq H' H'0 H'1 H'2 H'3.
cut (Fbounded b pq);
 [ intros Fb0
 | apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto; apply ClosestRoundedModeP with (precision := precision) ]; 
 auto.
case (Rle_or_lt 0 q); intros Rl2;
 [ idtac | cut (q <= 0)%R; [ intros Rl2' | apply Rlt_le; auto ] ].
repeat rewrite Rabs_right; auto with real.
apply plusClosestLowerBoundAux1 with (q := p); auto.
rewrite <- (Rabs_right q); auto with real.
apply (ClosestCompatible b radix (p + q)%R (q + p)%R pq pq); auto; try ring.
rewrite Rplus_comm; auto with real.
apply Rle_ge; unfold FtoRradix in |- *;
 apply
  RleRoundedR0
   with
     (b := b)
     (precision := precision)
     (P := Closest b radix)
     (r := (p + q)%R); auto.
apply ClosestRoundedModeP with (precision := precision); auto.
case (Rle_or_lt 0 p); intros Rl3;
 [ idtac | cut (p <= 0)%R; [ intros Rl3' | apply Rlt_le; auto ] ];
 auto with real.
replace 0%R with (0 + 0)%R; auto with real.
apply Rplus_le_reg_l with (r := (- p)%R).
replace (- p + 0)%R with (- p)%R; [ idtac | ring ].
replace (- p + (p + q))%R with (FtoRradix q); [ idtac | ring ].
rewrite <- (Faux.Rabsolu_left1 (FtoRradix p)); auto with real.
rewrite <- (Rabs_right (FtoRradix q)); auto with real.
repeat rewrite Faux.Rabsolu_left1; auto with real.
unfold FtoRradix in |- *; repeat rewrite <- (Fopp_correct 2%nat); auto.
apply plusClosestLowerBoundAux1 with (q := Fopp p); auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; rewrite Rabs_Ropp;
 rewrite <- Faux.Rabsolu_left1; auto with real.
apply
 (ClosestCompatible b radix (- (p + q))%R (Fopp q + Fopp p)%R (
    Fopp pq) (Fopp pq)); auto.
apply ClosestOpp; auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; ring.
apply oppBounded; auto.
apply oppBounded; auto.
apply oppBounded; auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; Contradict H'2.
unfold FtoRradix in |- *; rewrite <- (Ropp_involutive (FtoR radix pq));
 rewrite H'2; ring.
unfold FtoRradix in |- *;
 apply
  RleRoundedLessR0
   with
     (b := b)
     (precision := precision)
     (P := Closest b radix)
     (r := (p + q)%R); auto.
apply ClosestRoundedModeP with (precision := precision); auto.
case (Rle_or_lt 0 p); intros Rl3;
 [ idtac | cut (p <= 0)%R; [ intros Rl3' | apply Rlt_le; auto ] ];
 auto with real.
apply Rplus_le_reg_l with (r := (- q)%R).
replace (- q + 0)%R with (- q)%R; [ idtac | ring ].
replace (- q + (p + q))%R with (FtoRradix p); [ idtac | ring ].
rewrite <- (Rabs_right (FtoRradix p)); auto with real.
rewrite <- (Rabs_left (FtoRradix q)); auto with real.
replace 0%R with (0 + 0)%R; auto with real.
Qed.
 
Theorem plusClosestLowerBound :
 forall p q pq : float,
 Closest b radix (p + q) pq ->
 Fbounded b p ->
 Fbounded b q ->
 pq <> (p + q)%R :>R -> (/ radix * Rmax (Rabs p) (Rabs q) <= Rabs pq)%R.
intros p q pq H' H'0 H'1 H'2.
cut (Fbounded b pq);
 [ intros Fb0
 | apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto; apply ClosestRoundedModeP with (precision := precision) ]; 
 auto.
unfold Rmax in |- *.
case (Rle_dec (Rabs p) (Rabs q)); intros Rl1.
apply plusClosestLowerBoundAux2 with (p := p); auto.
apply plusClosestLowerBoundAux2 with (p := q); auto.
apply (ClosestCompatible b radix (p + q)%R (q + p)%R pq pq); auto; try ring.
rewrite Rplus_comm; auto.
case (Rle_or_lt (Rabs q) (Rabs p)); auto; intros H'3; Contradict Rl1;
 apply Rlt_le; auto.
Qed.
End F2.