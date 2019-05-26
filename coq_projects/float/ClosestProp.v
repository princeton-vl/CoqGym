(****************************************************************************
                                                                             
          IEEE754  :  ClosestProp                                                   
                                                                             
          Laurent Thery, Sylvie Boldo                                                      
                                                                             
  ******************************************************************************)
Require Export FroundProp.
Require Export Closest.
Section Fclosestp2.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem ClosestOpp :
 forall (p : float) (r : R),
 Closest b radix r p -> Closest b radix (- r) (Fopp p).
intros p r H'; split.
apply oppBounded; auto.
case H'; auto.
intros f H'0.
rewrite Fopp_correct.
replace (- FtoR radix p - - r)%R with (- (FtoR radix p - r))%R;
 [ idtac | ring ].
replace (FtoR radix f - - r)%R with (- (- FtoR radix f - r))%R;
 [ idtac | ring ].
rewrite <- Fopp_correct.
repeat rewrite Rabs_Ropp.
case H'; auto with float.
Qed.
 
Theorem ClosestFabs :
 forall (p : float) (r : R),
 Closest b radix r p -> Closest b radix (Rabs r) (Fabs p).
intros p r H'; case (Rle_or_lt 0 r); intros Rl0.
rewrite Rabs_right; auto with real.
replace (Fabs p) with p; auto.
unfold Fabs in |- *; apply floatEq; simpl in |- *; auto.
cut (0 <= Fnum p)%Z.
case (Fnum p); simpl in |- *; auto; intros p' H0; Contradict H0;
 apply Zlt_not_le; red in |- *; simpl in |- *; auto with zarith.
apply LeR0Fnum with (radix := radix); auto.
apply
 RleRoundedR0
  with (b := b) (precision := precision) (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto with real.
rewrite Faux.Rabsolu_left1; auto.
replace (Fabs p) with (Fopp p).
apply ClosestOpp; auto.
unfold Fabs in |- *; apply floatEq; simpl in |- *; auto.
cut (Fnum p <= 0)%Z.
case (Fnum p); simpl in |- *; auto; intros p' H0; Contradict H0;
 apply Zlt_not_le; red in |- *; simpl in |- *; auto with zarith.
apply R0LeFnum with (radix := radix); auto.
apply
 RleRoundedLessR0
  with (b := b) (precision := precision) (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
apply Rlt_le; auto.
apply Rlt_le; auto.
Qed.
 
Theorem ClosestUlp :
 forall (p : R) (q : float),
 Closest b radix p q -> (2%nat * Rabs (p - q) <= Fulp b radix precision q)%R.
intros p q H'.
case (Req_dec p q); intros Eqpq.
rewrite Eqpq.
replace (Rabs (q - q)) with 0%R;
 [ rewrite Rmult_0_r
 | replace (q - q)%R with 0%R; try ring; rewrite Rabs_right; auto with real ].
unfold Fulp in |- *; apply Rlt_le; auto with real arith.
replace (2%nat * Rabs (p - q))%R with (Rabs (p - q) + Rabs (p - q))%R;
 [ idtac | simpl in |- *; ring ].
case ClosestMinOrMax with (1 := H'); intros H'1.
apply Rle_trans with (Rabs (p - q) + Rabs (FNSucc b radix precision q - p))%R.
apply Rplus_le_compat_l.
rewrite <- (Rabs_Ropp (p - q)).
rewrite Ropp_minus_distr.
elim H'; auto.
intros H'0 H'2; apply H'2; auto.
apply FcanonicBound with (radix := radix); auto with float arith.
rewrite Rabs_right.
rewrite Rabs_right.
replace (p - q + (FNSucc b radix precision q - p))%R with
 (FNSucc b radix precision q - q)%R; [ idtac | ring ].
unfold FtoRradix in |- *; apply FulpSuc; auto.
case H'1; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
case MinMax with (3 := pGivesBound) (r := p) (p := q); auto with arith.
intros H'0 H'2; elim H'2; intros H'3 H'4; apply H'3; clear H'2; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
apply isMin_inv1 with (1 := H'1).
apply Rle_trans with (Rabs (p - q) + Rabs (p - FNPred b radix precision q))%R.
apply Rplus_le_compat_l.
rewrite <- (Rabs_Ropp (p - q));
 rewrite <- (Rabs_Ropp (p - FNPred b radix precision q)).
repeat rewrite Ropp_minus_distr.
elim H'; auto.
intros H'0 H'2; apply H'2; auto.
apply FcanonicBound with (radix := radix); auto with float arith.
rewrite <- (Rabs_Ropp (p - q)); rewrite Ropp_minus_distr.
rewrite Rabs_right.
rewrite Rabs_right.
replace (q - p + (p - FNPred b radix precision q))%R with
 (q - FNPred b radix precision q)%R; [ idtac | ring ].
unfold FtoRradix in |- *; apply FulpPred; auto.
case H'1; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
case MaxMin with (3 := pGivesBound) (r := p) (p := q); auto with arith.
intros H'0 H'2; elim H'2; intros H'3 H'4; apply H'3; clear H'2; auto.
apply Rge_minus; apply Rle_ge; auto with real float.
apply isMax_inv1 with (1 := H'1).
Qed.
 
Theorem ClosestExp :
 forall (p : R) (q : float),
 Closest b radix p q -> (2%nat * Rabs (p - q) <= powerRZ radix (Fexp q))%R.
intros p q H'.
apply Rle_trans with (Fulp b radix precision q).
apply (ClosestUlp p q); auto.
replace (powerRZ radix (Fexp q)) with (FtoRradix (Float 1%nat (Fexp q))).
apply (FulpLe b radix); auto.
apply
 RoundedModeBounded with (radix := radix) (P := Closest b radix) (r := p);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
ring.
Qed.
 
Theorem ClosestErrorExpStrict :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix x p ->
 q = (x - p)%R :>R -> q <> 0%R :>R -> (Fexp q < Fexp p)%Z.
intros.
case (Zle_or_lt (Fexp p) (Fexp q)); auto; intros Z1.
absurd (powerRZ radix (Fexp p) <= powerRZ radix (Fexp q))%R.
2: apply Rle_powerRZ; auto with real arith.
apply Rgt_not_le.
red in |- *; apply Rlt_le_trans with (2%nat * powerRZ radix (Fexp q))%R.
apply Rltdouble; auto with real arith.
apply Rle_trans with (2%nat * Fabs q)%R.
apply Rmult_le_compat_l; auto with real arith.
replace 0%R with (INR 0); auto with real arith.
replace (powerRZ radix (Fexp q)) with (FtoRradix (Float 1%nat (Fexp q)));
 auto.
apply (Fop.RleFexpFabs radix); auto with real zarith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
rewrite (Fabs_correct radix); auto with arith.
replace (FtoR radix q) with (x - p)%R; auto.
apply ClosestExp; auto.
Qed.
 
Theorem ClosestIdem :
 forall p q : float, Fbounded b p -> Closest b radix p q -> p = q :>R.
intros p q H' H'0.
case (Rabs_pos (q - p)); intros H1.
Contradict H1; apply Rle_not_lt.
replace 0%R with (Rabs (p - p)); [ case H'0; auto | idtac ].
replace (p - p)%R with 0%R; [ apply Rabs_R0; auto | ring ].
apply Rplus_eq_reg_l with (r := (- p)%R).
apply trans_eq with 0%R; [ ring | idtac ].
apply trans_eq with (q - p)%R; [ idtac | ring ].
generalize H1; unfold Rabs in |- *; case (Rcase_abs (q - p)); auto.
intros r H0; replace 0%R with (-0)%R; [ rewrite H0 | idtac ]; ring.
Qed.
 
Theorem ClosestM1 :
 forall (r1 r2 : R) (min max p q : float),
 isMin b radix r1 min ->
 isMax b radix r1 max ->
 (min + max < 2%nat * r2)%R ->
 Closest b radix r1 p -> Closest b radix r2 q -> (p <= q)%R.
intros r1 r2 min max p q H' H'0 H'1 H'2 H'3.
case (Rle_or_lt r2 max); intros H'4.
2: apply (ClosestMonotone b radix) with (p := r1) (q := r2); auto.
2: apply Rle_lt_trans with (FtoRradix max); auto.
2: apply isMax_inv1 with (1 := H'0).
case H'4; clear H'4; intros H'4.
2: replace (FtoRradix q) with (FtoRradix max).
2: case ClosestMinOrMax with (1 := H'2); intros H'5.
2: replace (FtoRradix p) with (FtoRradix min).
2: apply Rle_trans with r1.
2: apply isMin_inv1 with (1 := H').
2: apply isMax_inv1 with (1 := H'0).
2: apply MinEq with (1 := H'); auto.
2: replace (FtoRradix p) with (FtoRradix max); auto with real.
2: apply MaxEq with (1 := H'0); auto.
2: apply ClosestIdem; auto.
2: case H'0; auto.
2: rewrite <- H'4; auto.
cut (min < r2)%R.
2: apply Rmult_lt_reg_l with (r := INR 2); auto with real.
2: replace (2%nat * min)%R with (min + min)%R;
    [ idtac | simpl in |- *; ring ].
2: apply Rle_lt_trans with (2 := H'1).
2: apply Rplus_le_compat_l; auto with real.
2: apply Rle_trans with r1.
2: apply isMin_inv1 with (1 := H').
2: apply isMax_inv1 with (1 := H'0).
intros H'5.
replace (FtoRradix q) with (FtoRradix max).
case ClosestMinOrMax with (1 := H'2); intros H'6.
replace (FtoRradix p) with (FtoRradix min).
apply Rle_trans with r1.
apply isMin_inv1 with (1 := H').
apply isMax_inv1 with (1 := H'0).
apply MinEq with (1 := H'); auto.
replace (FtoRradix p) with (FtoRradix max); auto with real.
apply MaxEq with (1 := H'0); auto.
apply sym_eq.
apply (ClosestMaxEq b radix) with (r := r2) (min := min); auto.
apply isMinComp with (2 := H'0); auto.
apply isMaxComp with (1 := H'); auto.
Qed.
 
Theorem FmultRadixInv :
 forall (x z : float) (y : R),
 Fbounded b x ->
 Closest b radix y z -> (/ 2%nat * x < y)%R -> (/ 2%nat * x <= z)%R.
intros x z y H' H'0 H'1.
case MinEx with (r := (/ 2%nat * x)%R) (3 := pGivesBound); auto with arith.
intros min isMin.
case MaxEx with (r := (/ 2%nat * x)%R) (3 := pGivesBound); auto with arith.
intros max isMax.
case (Rle_or_lt y max); intros Rl1.
case Rl1; clear Rl1; intros Rl1.
replace (FtoRradix z) with (FtoRradix max).
apply isMax_inv1 with (1 := isMax).
apply sym_eq.
unfold FtoRradix in |- *;
 apply ClosestMaxEq with (b := b) (r := y) (min := min); 
 auto.
apply isMinComp with (r1 := (/ 2%nat * x)%R) (max := max); auto.
apply Rle_lt_trans with (2 := H'1); auto.
apply isMin_inv1 with (1 := isMin).
apply isMaxComp with (r1 := (/ 2%nat * x)%R) (min := min); auto.
apply Rle_lt_trans with (2 := H'1); auto.
apply isMin_inv1 with (1 := isMin).
replace (FtoR radix min + FtoR radix max)%R with (FtoRradix x).
apply Rmult_lt_reg_l with (r := (/ 2%nat)%R); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l; try rewrite Rmult_1_l; auto with real.
unfold FtoRradix in |- *; apply (div2IsBetween b radix precision); auto.
cut (Closest b radix max z); [ intros C0 | idtac ].
replace (FtoRradix z) with (FtoRradix max); auto.
rewrite <- Rl1; auto.
apply Rlt_le; auto.
apply ClosestIdem; auto.
case isMax; auto.
apply (ClosestCompatible b radix y max z z); auto.
case H'0; auto.
apply Rle_trans with (FtoRradix max); auto.
apply isMax_inv1 with (1 := isMax).
apply (ClosestMonotone b radix (FtoRradix max) y); auto.
apply (RoundedModeProjectorIdem b radix (Closest b radix)); auto.
apply ClosestRoundedModeP with (precision := precision); auto.
case isMax; auto.
Qed.
 
Theorem ClosestErrorBound :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Closest b radix x p ->
 q = (x - p)%R :>R -> (Rabs q <= Float 1%nat (Fexp p) * / 2%nat)%R.
intros p q x H H0 H1.
apply Rle_trans with (Fulp b radix precision p * / 2%nat)%R.
rewrite H1.
replace (Rabs (x - p)) with (2%nat * Rabs (x - p) * / 2%nat)%R;
 [ idtac | field; auto with real ].
apply Rmult_le_compat_r; auto with real.
apply ClosestUlp; auto.
apply Rmult_le_compat_r.
apply Rlt_le.
apply Rinv_0_lt_compat; auto with real.
unfold FtoRradix in |- *; apply FulpLe; auto.
Qed.
 
Theorem ClosestErrorExp :
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix x p ->
 q = (x - p)%R :>R ->
 exists error : float,
   Fbounded b error /\
   error = q :>R /\ (Fexp error <= Zmax (Fexp p - precision) (- dExp b))%Z.
intros p q x H H0 H1 H2; exists (Fnormalize radix b precision q).
cut (Fcanonic radix b (Fnormalize radix b precision q));
 [ intros C1 | apply FnormalizeCanonic; auto with arith ].
split.
apply FcanonicBound with (radix := radix); auto.
split.
apply (FnormalizeCorrect radix); auto.
case C1; intros C2.
apply Zle_trans with (Fexp p - precision)%Z; auto with zarith.
apply Zplus_le_reg_l with (Z_of_nat precision).
replace (precision + (Fexp p - precision))%Z with (Fexp p); [ idtac | ring ].
replace (precision + Fexp (Fnormalize radix b precision q))%Z with
 (Zsucc (Zpred precision + Fexp (Fnormalize radix b precision q)));
 [ idtac | unfold Zpred, Zsucc in |- *; ring ].
apply Zlt_le_succ.
apply Zlt_powerRZ with (IZR radix); auto with real zarith.
rewrite powerRZ_add; auto with real zarith.
apply
 Rle_lt_trans
  with
    (Zabs (Fnum (Fnormalize radix b precision q)) *
     powerRZ radix (Fexp (Fnormalize radix b precision q)))%R.
apply Rmult_le_compat_r; auto with real zarith.
replace (Zpred precision) with
 (Z_of_nat (pred (digit radix (Fnum (Fnormalize radix b precision q))))).
rewrite <- Zpower_nat_Z_powerRZ.
apply Rle_IZR; apply digitLess; auto with real zarith.
change (~ is_Fzero (Fnormalize radix b precision q)) in |- *;
 apply (FnormalNotZero radix b); auto with float.
change
  (Z_of_nat (pred (Fdigit radix (Fnormalize radix b precision q))) =
   Zpred precision) in |- *.
rewrite FnormalPrecision with (precision := precision) (4 := C2);
 auto with zarith arith.
apply inj_pred; auto with arith.
change (Fabs (Fnormalize radix b precision q) < powerRZ radix (Fexp p))%R
 in |- *.
rewrite (Fabs_correct radix); auto; rewrite (FnormalizeCorrect radix); auto.
apply Rle_lt_trans with (Float 1%nat (Fexp p) * / 2%nat)%R.
apply ClosestErrorBound with (x := x); auto.
unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *.
pattern (powerRZ radix (Fexp p)) at 2 in |- *;
 replace (powerRZ radix (Fexp p)) with (powerRZ radix (Fexp p) * 1)%R;
 [ idtac | ring ].
replace (1 * powerRZ radix (Fexp p))%R with (powerRZ radix (Fexp p));
 [ apply Rmult_lt_compat_l | ring ].
apply powerRZ_lt; auto with arith real.
pattern 1%R at 3 in |- *; replace 1%R with (/ 1)%R.
apply Rinv_1_lt_contravar; auto with real.
replace 2%R with (INR 2); auto with real arith.
apply Zle_trans with (- dExp b)%Z; auto with float zarith.
case C2.
intros H3 (H4, H5); rewrite H4; auto with zarith.
Qed.
 
Theorem ClosestErrorBoundNormal_aux :
 forall (x : R) (p : float),
 Closest b radix x p ->
 Fnormal radix b (Fnormalize radix b precision p) ->
 (Rabs (x - p) <= Rabs p * (/ 2%nat * (radix * / Zpos (vNum b))))%R.
intros x p H H'.
apply Rle_trans with (/ 2%nat * Fulp b radix precision p)%R.
replace (Rabs (x - FtoRradix p)) with
 (/ 2%nat * (2%nat * Rabs (x - FtoRradix p)))%R.
apply Rmult_le_compat_l; auto with real.
apply ClosestUlp; auto.
rewrite <- Rmult_assoc; rewrite Rinv_l; simpl in |- *; auto with real.
apply
 Rle_trans with (/ 2%nat * (Rabs p * (radix * / Zpos (vNum b))))%R;
 [ apply Rmult_le_compat_l | right; ring; ring ].
apply Rlt_le; apply Rinv_0_lt_compat; auto with real arith.
unfold Fulp in |- *.
replace (Fexp (Fnormalize radix b precision p)) with
 (Fexp (Fnormalize radix b precision p) + precision + - precision)%Z;
 [ idtac | ring ].
rewrite powerRZ_add; auto with real zarith.
apply Rle_trans with (Rabs p * radix * powerRZ radix (- precision))%R;
 [ apply Rmult_le_compat_r | right ]; auto with real zarith.
2: rewrite pGivesBound; simpl in |- *.
2: rewrite powerRZ_Zopp; auto with real zarith; rewrite Zpower_nat_Z_powerRZ;
    auto with real zarith; ring.
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p));
 [ idtac | apply (FnormalizeCorrect radix) ]; auto.
rewrite <- (Fabs_correct radix); unfold FtoR in |- *; simpl in |- *;
 auto with arith.
rewrite powerRZ_add; auto with real zarith.
replace
 (Zabs (Fnum (Fnormalize radix b precision p)) *
  powerRZ radix (Fexp (Fnormalize radix b precision p)) * radix)%R with
 (powerRZ radix (Fexp (Fnormalize radix b precision p)) *
  (Zabs (Fnum (Fnormalize radix b precision p)) * radix))%R; 
 [ idtac | ring ].
apply Rmult_le_compat_l; auto with arith real.
rewrite <- Zpower_nat_Z_powerRZ; auto with real zarith.
rewrite <- Rmult_IZR; apply Rle_IZR.
rewrite <- pGivesBound; pattern radix at 2 in |- *;
 rewrite <- (Zabs_eq radix); auto with zarith.
rewrite <- Zabs_Zmult.
rewrite Zmult_comm; elim H'; auto.
Qed.
 
Theorem ClosestErrorBound2 :
 forall (x : R) (p : float),
 Closest b radix x p ->
 (Rabs (x - p) <=
  Rmax (Rabs p * (/ 2%nat * (radix * / Zpos (vNum b))))
    (/ 2%nat * powerRZ radix (- dExp b)))%R.
intros x p H.
cut (Fcanonic radix b (Fnormalize radix b precision p));
 [ intros tmp; Casec tmp; intros Fs | idtac ].
3: apply FnormalizeCanonic; auto with arith.
3: apply
    RoundedModeBounded with (radix := radix) (P := Closest b radix) (r := x);
    auto.
3: apply ClosestRoundedModeP with (precision := precision); auto.
apply
 Rle_trans with (Rabs p * (/ 2%nat * (radix * / Zpos (vNum b))))%R;
 [ idtac | apply RmaxLess1 ].
apply ClosestErrorBoundNormal_aux; auto.
apply Rle_trans with (/ 2%nat * Fulp b radix precision p)%R.
replace (Rabs (x - FtoRradix p)) with
 (/ 2%nat * (2%nat * Rabs (x - FtoRradix p)))%R.
apply Rmult_le_compat_l; auto with real.
apply ClosestUlp; auto.
rewrite <- Rmult_assoc; rewrite Rinv_l; simpl in |- *; auto with real.
elim Fs; intros H1 H2; elim H2; intros; clear H2.
unfold Fulp in |- *; rewrite H0; apply RmaxLess2.
Qed.
 
Theorem ClosestErrorBoundNormal :
 forall (x : R) (p : float),
 Closest b radix x p ->
 Fnormal radix b (Fnormalize radix b precision p) ->
 (Rabs (x - p) <= Rabs p * (/ 2%nat * powerRZ radix (Zsucc (- precision))))%R.
intros x p H H1.
apply
 Rle_trans
  with (Rabs (FtoRradix p) * (/ 2%nat * (radix * / Zpos (vNum b))))%R;
 [ apply ClosestErrorBoundNormal_aux; auto | right ].
replace (powerRZ radix (Zsucc (- precision))) with
 (radix * / Zpos (vNum b))%R; auto with real.
rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ.
rewrite Rinv_powerRZ; auto with real zarith.
rewrite powerRZ_Zs; auto with real zarith.
Qed.
 
Theorem ClosestPropHigham25 :
 forall (x : R) (p : float),
 Closest b radix x p ->
 exists delta : R,
   (exists nu : R,
      (x / (1 + delta) + nu)%R = FtoRradix p /\
      (Rabs delta <= / 2%nat * powerRZ radix (Zsucc (- precision)))%R /\
      (Rabs nu <= / 2%nat * powerRZ radix (- dExp b))%R /\
      (delta * nu)%R = 0%R /\
      (Fnormal radix b (Fnormalize radix b precision p) -> nu = 0%R) /\
      (Fsubnormal radix b (Fnormalize radix b precision p) -> delta = 0%R)).
intros x p H.
cut (Fcanonic radix b (Fnormalize radix b precision p));
 [ intros tmp; Casec tmp; intros Fs | idtac ].
3: apply FnormalizeCanonic; auto with arith.
3: apply
    RoundedModeBounded with (radix := radix) (P := Closest b radix) (r := x);
    auto.
3: apply ClosestRoundedModeP with (precision := precision); auto.
cut (~ is_Fzero (Fnormalize radix b precision p));
 [ unfold is_Fzero in |- *; intros tmp
 | apply FnormalNotZero with radix b; auto ].
cut (FtoRradix p <> 0%R); [ intros H1; clear tmp | unfold FtoRradix in |- * ].
2: rewrite <- FnormalizeCorrect with radix b precision p; auto;
    unfold FtoR in |- *; simpl in |- *.
2: apply Rmult_integral_contrapositive; split; auto with real zarith.
exists ((x - p) / p)%R; exists 0%R.
split; [ case (Req_dec x 0); intros H2 | idtac ].
repeat rewrite H2; unfold Rdiv in |- *.
ring_simplify.
rewrite <- FzeroisZero with radix b; unfold FtoRradix in |- *.
cut (ProjectorP b radix (Closest b radix));
 [ unfold ProjectorP in |- *; intros H3
 | apply RoundedProjector; auto with float ].
apply H3; auto with float zarith.
replace (FtoR radix (Fzero (- dExp b))) with x; auto with real.
rewrite H2; unfold Fzero, FtoR in |- *; simpl in |- *; ring.
apply ClosestRoundedModeP with precision; auto with zarith.
apply sym_eq; apply trans_eq with (x / (1 + (x - p) / p))%R; [ idtac | ring ].
replace (1 + (x - FtoRradix p) / FtoRradix p)%R with (x / p)%R;
 unfold Rdiv in |- *.
rewrite Rinv_mult_distr; auto with real; rewrite Rinv_involutive; auto;
 rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real.
ring_simplify; rewrite Rinv_l; auto with real; ring.
split.
apply Rmult_le_reg_l with (Rabs p); [ apply Rabs_pos_lt; auto | idtac ].
apply Rle_trans with (Rabs (x - FtoRradix p));
 [ right | apply ClosestErrorBoundNormal; auto ].
unfold Rdiv in |- *; rewrite Rabs_mult; rewrite Rabs_Rinv; auto.
rewrite Rmult_comm; rewrite Rmult_assoc; rewrite Rinv_l; auto with real.
apply Rabs_no_R0; exact H1.
split; [ rewrite Rabs_R0; apply Rmult_le_pos; auto with real zarith | idtac ].
split; [ ring | idtac ].
split; [ auto with real | intros H2 ].
absurd
 (Fnormal radix b (Fnormalize radix b precision p) /\
  Fsubnormal radix b (Fnormalize radix b precision p)).
apply NormalNotSubNormal; auto.
split; auto.
exists 0%R; exists (p - x)%R.
split; [ unfold Rdiv in |- *; ring_simplify (1 + 0)%R; rewrite Rinv_1; ring | idtac ].
split; [ rewrite Rabs_R0; apply Rmult_le_pos; auto with real zarith | idtac ].
split.
apply Rle_trans with (/ 2%nat * Fulp b radix precision p)%R.
rewrite <- Rabs_Ropp;
 replace (- (FtoRradix p - x))%R with (x - FtoRradix p)%R; 
 [ idtac | ring ].
replace (Rabs (x - FtoRradix p)) with
 (/ 2%nat * (2%nat * Rabs (x - FtoRradix p)))%R.
apply Rmult_le_compat_l; auto with real; apply ClosestUlp; auto.
rewrite <- Rmult_assoc; rewrite Rinv_l; simpl in |- *; auto with real.
elim Fs; intros H1 H2; elim H2; intros; clear H2.
unfold Fulp in |- *; rewrite H0; auto with real.
split; [ ring | idtac ].
split; [ intros H2 | auto with real ].
absurd
 (Fnormal radix b (Fnormalize radix b precision p) /\
  Fsubnormal radix b (Fnormalize radix b precision p)).
apply NormalNotSubNormal; auto.
split; auto.
Qed.
 
Theorem FpredUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 < x)%R ->
 (FPred b radix precision x +
  Fulp b radix precision (FPred b radix precision x))%R = x.
intros x Hx H.
apply sym_eq;
 apply Rplus_eq_reg_l with (- FtoRradix (FPred b radix precision x))%R.
apply trans_eq with (Fulp b radix precision (FPred b radix precision x));
 [ idtac | ring ].
apply trans_eq with (FtoRradix x - FtoRradix (FPred b radix precision x))%R;
 [ ring | idtac ].
unfold FtoRradix in |- *; rewrite <- Fminus_correct; auto with zarith;
 fold FtoRradix in |- *.
pattern x at 1 in |- *;
 replace x with (FSucc b radix precision (FPred b radix precision x));
 [ idtac | apply FSucPred; auto with zarith arith ].
unfold FtoRradix in |- *; apply FSuccUlpPos; auto with zarith arith.
apply FPredCanonic; auto with zarith arith.
apply R0RltRlePred; auto with zarith arith real.
Qed.
 
Theorem FulpFPredLe :
 forall f : float,
 Fbounded b f ->
 Fcanonic radix b f ->
 (Fulp b radix precision f <=
  radix * Fulp b radix precision (FPred b radix precision f))%R.
intros f Hf1 Hf2; unfold Fulp in |- *.
replace (Fnormalize radix b precision f) with f;
 [ idtac
 | apply
    FcanonicUnique with (radix := radix) (b := b) (precision := precision);
    auto with float arith zarith ].
2: apply sym_eq; apply FnormalizeCorrect; auto with arith zarith.
replace (Fnormalize radix b precision (FPred b radix precision f)) with
 (FPred b radix precision f);
 [ idtac
 | apply
    FcanonicUnique with (radix := radix) (b := b) (precision := precision);
    auto with float arith zarith ].
2: apply sym_eq; apply FnormalizeCorrect; auto with arith zarith.
pattern (IZR radix) at 2 in |- *; replace (IZR radix) with (powerRZ radix 1);
 [ idtac | simpl in |- *; auto with arith zarith real ].
rewrite <- powerRZ_add; auto with zarith real.
apply Rle_powerRZ; auto with zarith real.
replace (1 + Fexp (FPred b radix precision f))%Z with
 (Zsucc (Fexp (FPred b radix precision f))); auto with zarith.
unfold FPred in |- *.
generalize (Z_eq_bool_correct (Fnum f) (- pPred (vNum b)));
 case (Z_eq_bool (Fnum f) (- pPred (vNum b))); intros H1;
 [ simpl in |- *; auto with zarith | idtac ].
generalize (Z_eq_bool_correct (Fnum f) (nNormMin radix precision));
 case (Z_eq_bool (Fnum f) (nNormMin radix precision)); 
 intros H2; [ idtac | simpl in |- *; auto with zarith ].
generalize (Z_eq_bool_correct (Fexp f) (- dExp b));
 case (Z_eq_bool (Fexp f) (- dExp b)); intros H3; simpl in |- *;
 auto with zarith.
Qed.
 
Theorem ClosestErrorBoundNormal2_aux :
 forall (x : R) (p : float),
 Closest b radix x p ->
 Fnormal radix b p ->
 Fnormal radix b (Fnormalize radix b precision (FPred b radix precision p)) ->
 (0 < x)%R ->
 (x < p)%R ->
 (Rabs (x - p) <= Rabs x * (/ 2%nat * powerRZ radix (Zsucc (- precision))))%R.
intros x p H1 H2 H0 H3 H4.
cut (Fcanonic radix b p); [ intros H5 | left; auto ].
cut (Fbounded b p); [ intros H6 | elim H2; auto ].
cut (0 < p)%R; [ intros H7 | apply Rlt_trans with x; auto ].
cut (FPred b radix precision p < x)%R; [ intros H' | idtac ].
apply
 Rle_trans
  with (/ 2%nat * Fulp b radix precision (FPred b radix precision p))%R.
case
 (Rle_or_lt (Rabs (x - FtoRradix p))
    (/ 2%nat * Fulp b radix precision (FPred b radix precision p))); 
 auto; intros H8.
absurd (Rabs (p - x) <= Rabs (FPred b radix precision p - x))%R.
2: generalize H1; unfold Closest in |- *; intros H9; elim H9; intros tmp H10.
2: clear tmp; apply H10; auto with float zarith arith.
apply Rlt_not_le; rewrite Rabs_left; auto with real.
apply Rle_lt_trans with (p - FPred b radix precision p + (x - p))%R;
 [ right; ring | idtac ].
pattern (FtoRradix p) at 1 in |- *; rewrite <- FpredUlpPos with p;
 auto with real.
apply
 Rle_lt_trans
  with (Fulp b radix precision (FPred b radix precision p) + (x - p))%R;
 [ right; ring | idtac ].
apply
 Rle_lt_trans
  with
    (Fulp b radix precision (FPred b radix precision p) +
     - (/ 2%nat * Fulp b radix precision (FPred b radix precision p)))%R;
 [ apply Rplus_le_compat_l | idtac ].
apply Ropp_le_cancel; rewrite Ropp_involutive; rewrite <- Rabs_left;
 auto with real.
apply
 Rle_lt_trans
  with (/ 2%nat * Fulp b radix precision (FPred b radix precision p))%R.
right;
 apply
  trans_eq
   with
     ((1 + - / 2%nat) * Fulp b radix precision (FPred b radix precision p))%R;
 [ ring | idtac ].
replace (1 + - / 2%nat)%R with (/ 2%nat)%R;
 [ ring | simpl; field; auto with arith real; simpl in |- *; ring ].
rewrite <- Rabs_Ropp; replace (- (FtoRradix p - x))%R with (x - p)%R; auto;
 ring.
apply
 Rle_trans with (/ 2%nat * (Rabs x * powerRZ radix (Zsucc (- precision))))%R;
 [ apply Rmult_le_compat_l; auto with real arith | right; ring ].
apply
 Rle_trans
  with
    (Rabs (FPred b radix precision p) * powerRZ radix (Zsucc (- precision)))%R.
unfold Fulp in |- *;
 replace (Fexp (Fnormalize radix b precision (FPred b radix precision p)))
  with
  (Fexp (Fnormalize radix b precision (FPred b radix precision p)) +
   precision + - precision)%Z; [ idtac | ring ].
rewrite powerRZ_add; auto with real zarith.
apply
 Rle_trans
  with
    (Rabs (FPred b radix precision p) * radix * powerRZ radix (- precision))%R;
 [ apply Rmult_le_compat_r | right ]; auto with real zarith.
2: rewrite powerRZ_Zs; auto with real zarith; ring.
replace (FtoRradix (FPred b radix precision p)) with
 (FtoRradix (Fnormalize radix b precision (FPred b radix precision p)));
 [ idtac | apply (FnormalizeCorrect radix) ]; auto.
rewrite <- (Fabs_correct radix); unfold FtoR in |- *; simpl in |- *;
 auto with arith.
rewrite powerRZ_add; auto with real zarith.
apply
 Rle_trans
  with
    (powerRZ radix
       (Fexp (Fnormalize radix b precision (FPred b radix precision p))) *
     (Zabs (Fnum (Fnormalize radix b precision (FPred b radix precision p))) *
      radix))%R; [ idtac | right; ring ].
apply Rmult_le_compat_l; auto with arith real.
rewrite <- Zpower_nat_Z_powerRZ; auto with real zarith; rewrite <- Rmult_IZR.
apply Rle_IZR; rewrite <- pGivesBound; pattern radix at 3 in |- *;
 rewrite <- (Zabs_eq radix); auto with zarith; rewrite <- Zabs_Zmult;
 rewrite Zmult_comm; elim H0; auto.
apply Rmult_le_compat_r; auto with real zarith.
repeat rewrite Rabs_right; auto with real; apply Rle_ge; auto with real.
unfold FtoRradix in |- *; apply R0RltRlePred; auto with real arith.
case (Rle_or_lt 0 (FtoRradix (FPred b radix precision p) - x)); intros H9.
absurd (Rabs (p - x) <= Rabs (FPred b radix precision p - x))%R.
apply Rlt_not_le; repeat rewrite Rabs_right; try apply Rle_ge; auto with real.
unfold Rminus in |- *; apply Rplus_lt_compat_r; auto with real float zarith.
unfold FtoRradix in |- *; apply FPredLt; auto with real float zarith.
generalize H1; unfold Closest in |- *; intros H'; elim H'; intros tmp H10.
clear tmp; apply H10; auto with float zarith arith.
apply Rplus_lt_reg_l with (- x)%R; auto with real.
ring_simplify (- x + x)%R; apply Rle_lt_trans with (2 := H9); right; ring.
Qed.
 
End Fclosestp2.
Hint Resolve ClosestOpp ClosestFabs ClosestUlp: float.