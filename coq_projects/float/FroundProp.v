(****************************************************************************
                                                                             
          IEEE754  :  FroundProp                                                     
                                                                             
          Laurent Thery, Sylvie Boldo                                                      
                                                                             
  ******************************************************************************)
Require Export Fround.
Require Export MSB.
Section FRoundP.
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
 
Definition Fulp (p : float) :=
  powerRZ radix (Fexp (Fnormalize radix b precision p)).
 
Theorem FulpComp :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> p = q :>R -> Fulp p = Fulp q.
intros p q H' H'0 H'1; unfold Fulp in |- *.
rewrite
 FcanonicUnique
                with
                (p := Fnormalize radix b precision p)
               (q := Fnormalize radix b precision q)
               (3 := pGivesBound); auto with float arith.
apply trans_eq with (FtoR radix p).
apply FnormalizeCorrect; auto.
apply trans_eq with (FtoR radix q); auto.
apply sym_eq; apply FnormalizeCorrect; auto.
Qed.
 
Theorem FulpLe :
 forall p : float, Fbounded b p -> (Fulp p <= Float 1 (Fexp p))%R.
intros p H'; unfold Fulp, FtoRradix, FtoR, Fnormalize in |- *; simpl in |- *;
 rewrite Rmult_1_l.
case (Z_zerop (Fnum p)); simpl in |- *; auto.
intros H'0; apply (Rle_powerRZ radix (- dExp b) (Fexp p));
 auto with float real zarith.
intros H'0; apply Rle_powerRZ; auto with real zarith arith.
Qed.
 
Theorem Fulp_zero :
 forall x : float, is_Fzero x -> Fulp x = powerRZ radix (- dExp b).
intros x; unfold is_Fzero, Fulp, Fnormalize in |- *; case (Z_zerop (Fnum x));
 simpl in |- *; auto.
intros H' H'0; Contradict H'; auto.
Qed.
 
Theorem FulpLe2 :
 forall p : float,
 Fbounded b p ->
 Fnormal radix b (Fnormalize radix b precision p) ->
 (Fulp p <= Rabs p * powerRZ radix (Zsucc (- precision)))%R.
intros p H1 H2; unfold Fulp in |- *.
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p));
 [ idtac | unfold FtoRradix in |- *; apply FnormalizeCorrect; auto ].
apply Rmult_le_reg_l with (powerRZ radix (Zpred precision)).
apply powerRZ_lt; auto with real arith.
replace
 (powerRZ radix (Zpred precision) *
  (Rabs (Fnormalize radix b precision p) *
   powerRZ radix (Zsucc (- precision))))%R with
 (Rabs (Fnormalize radix b precision p)).
unfold FtoRradix in |- *; rewrite <- Fabs_correct; auto with arith real.
unfold Fabs, FtoR in |- *; simpl in |- *.
apply Rmult_le_compat_r; [ apply powerRZ_le | rewrite <- inj_pred ];
 auto with real arith zarith.
rewrite <- Zpower_nat_Z_powerRZ.
replace (Zpower_nat radix (pred precision)) with (nNormMin radix precision);
 auto; apply Rle_IZR.
apply pNormal_absolu_min with b; auto with arith zarith real.
apply
 trans_eq
  with
    (Rabs (Fnormalize radix b precision p) *
     (powerRZ radix (Zpred precision) * powerRZ radix (Zsucc (- precision))))%R;
 [ idtac | ring ].
rewrite <- powerRZ_add; auto with zarith real.
replace (Zpred precision + Zsucc (- precision))%Z with 0%Z;
 [ simpl in |- *; ring | unfold Zsucc, Zpred in |- *; ring ];
 auto with real zarith.
Qed.
 
Theorem FulpGe :
 forall p : float,
 Fbounded b p -> (Rabs p <= (powerRZ radix precision - 1) * Fulp p)%R.
intros p H.
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p));
 [ idtac | unfold FtoRradix in |- *; apply FnormalizeCorrect; auto ].
unfold FtoRradix in |- *; rewrite <- Fabs_correct; auto with arith real.
unfold FtoR in |- *; simpl in |- *; unfold Fulp in |- *.
apply Rmult_le_compat_r; [ apply powerRZ_le | idtac ];
 auto with real arith zarith.
apply Rle_trans with (IZR (Zpred (Zpos (vNum b))));
 [ apply Rle_IZR; auto with float zarith | idtac ].
unfold Zpred in |- *; right; rewrite pGivesBound; replace 1%R with (IZR 1);
 auto with real.
rewrite <- Zpower_nat_Z_powerRZ; rewrite Z_R_minus;auto.
Qed.
 
Theorem LeFulpPos :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y -> (0 <= x)%R -> (x <= y)%R -> (Fulp x <= Fulp y)%R.
intros x y Hx Hy H1 H2; unfold Fulp in |- *.
apply Rle_powerRZ; auto with real zarith.
apply Fcanonic_Rle_Zle with radix b precision; auto with zarith arith.
apply FnormalizeCanonic; auto with zarith arith.
apply FnormalizeCanonic; auto with zarith arith.
repeat rewrite FnormalizeCorrect; auto with zarith arith real.
repeat rewrite Rabs_right; auto with zarith arith real.
apply Rge_trans with (FtoRradix x); auto with real.
Qed.
 
Theorem FulpSucCan :
 forall p : float,
 Fcanonic radix b p -> (FSucc b radix precision p - p <= Fulp p)%R.
intros p H'.
replace (Fulp p) with (powerRZ radix (Fexp p)).
2: unfold Fulp in |- *; replace (Fnormalize radix b precision p) with p; auto;
    apply sym_equal; apply FcanonicUnique with (3 := pGivesBound);
    auto with arith; apply FnormalizeCanonic || apply FnormalizeCorrect;
    auto with float zarith.
2: apply FcanonicBound with (1 := H'); auto with float zarith.
unfold FtoRradix in |- *; rewrite <- Fminus_correct; auto with zarith.
case (Z_eq_dec (Fnum p) (- nNormMin radix precision)); intros H1'.
case (Z_eq_dec (Fexp p) (- dExp b)); intros H2'.
rewrite FSuccDiff2; auto with arith.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l; auto with real.
rewrite FSuccDiff3; auto with arith.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l.
apply Rlt_le; apply Rlt_powerRZ; auto with real zarith.
unfold Zpred in |- *; auto with zarith.
rewrite FSuccDiff1; auto with arith.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l; auto with real.
Qed.
 
Theorem FulpSuc :
 forall p : float,
 Fbounded b p -> (FNSucc b radix precision p - p <= Fulp p)%R.
intros p H'.
replace (Fulp p) with (Fulp (Fnormalize radix b precision p)).
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p)).
unfold FNSucc in |- *; apply FulpSucCan; auto with float arith.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
apply FulpComp; auto with float arith.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
Qed.
 
Theorem FulpPredCan :
 forall p : float,
 Fcanonic radix b p -> (p - FPred b radix precision p <= Fulp p)%R.
intros p H'.
replace (Fulp p) with (powerRZ radix (Fexp p)).
2: unfold Fulp in |- *; replace (Fnormalize radix b precision p) with p; auto;
    apply sym_equal; apply FcanonicUnique with (3 := pGivesBound);
    auto with arith; apply FnormalizeCanonic || apply FnormalizeCorrect;
    auto with arith.
unfold FtoRradix in |- *; rewrite <- Fminus_correct; auto with arith.
case (Z_eq_dec (Fnum p) (nNormMin radix precision)); intros H1'.
case (Z_eq_dec (Fexp p) (- dExp b)); intros H2'.
rewrite FPredDiff2; auto with arith.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l; auto with real.
rewrite FPredDiff3; auto with arith.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l; auto with real.
apply Rlt_le; apply Rlt_powerRZ; auto with real zarith.
replace 1%R with (INR 1); auto with real arith.
unfold Zpred in |- *; auto with zarith.
rewrite FPredDiff1; auto with arith.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l; auto with real.
apply FcanonicBound with (1 := H').
Qed.
 
Theorem FulpPred :
 forall p : float,
 Fbounded b p -> (p - FNPred b radix precision p <= Fulp p)%R.
intros p H'.
replace (Fulp p) with (Fulp (Fnormalize radix b precision p)).
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p)).
unfold FNPred in |- *; apply FulpPredCan; auto with float arith.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
apply FulpComp; auto with float arith.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
Qed.
 
Theorem FSuccDiffPos :
 forall x : float,
 (0 <= x)%R ->
 Fminus radix (FSucc b radix precision x) x = Float 1%nat (Fexp x) :>R.
intros x H.
unfold FtoRradix in |- *; apply FSuccDiff1; auto with arith.
Contradict H; unfold FtoRradix, FtoR in |- *; simpl in |- *; rewrite H.
apply Rlt_not_le.
replace 0%R with (0 * powerRZ radix (Fexp x))%R; [ idtac | ring ].
apply Rlt_monotony_exp; auto with real arith.
generalize (nNormPos _ radixMoreThanOne precision);
 replace 0%R with (IZR (- 0%nat)); auto with real zarith arith.
Qed.
 
Theorem FulpFPredGePos :
 forall f : float,
 Fbounded b f ->
 Fcanonic radix b f ->
 (0 < f)%R -> (Fulp (FPred b radix precision f) <= Fulp f)%R.
intros f Hf1 Hf2 H.
apply LeFulpPos; auto with zarith float; unfold FtoRradix in |- *.
apply R0RltRlePred; auto with arith.
apply Rlt_le; apply FPredLt; auto with arith.
Qed.
 
Theorem CanonicFulp :
 forall p : float, Fcanonic radix b p -> Fulp p = Float 1%nat (Fexp p).
intros p H; unfold Fulp in |- *.
rewrite FcanonicFnormalizeEq; auto with arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
Qed.
 
Theorem FSuccUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 <= x)%R -> Fminus radix (FSucc b radix precision x) x = Fulp x :>R.
intros x H H0; rewrite CanonicFulp; auto.
apply FSuccDiffPos; auto.
Qed.
 
Theorem FNSuccUlpPos :
 forall x : float,
 Fcanonic radix b x ->
 (0 <= x)%R -> Fminus radix (FNSucc b radix precision x) x = Fulp x :>R.
intros x H H0.
unfold FNSucc in |- *.
rewrite FcanonicFnormalizeEq; auto with arith.
apply FSuccUlpPos; auto.
Qed.
 
Theorem FulpFabs : forall f : float, Fulp f = Fulp (Fabs f) :>R.
intros f; unfold Fulp in |- *; case (Rle_or_lt 0 f); intros H'.
replace (Fabs f) with f; auto; unfold Fabs in |- *; apply floatEq;
 simpl in |- *; auto with zarith real.
apply sym_eq; apply Zabs_eq; apply LeR0Fnum with radix; auto with zarith real.
replace (Fabs f) with (Fopp f);
 [ rewrite Fnormalize_Fopp | apply floatEq; simpl in |- * ]; 
 auto with arith.
apply sym_eq; apply Zabs_eq_opp; apply R0LeFnum with radix;
 auto with zarith real.
Qed.
 
Theorem RoundedModeUlp :
 forall P,
 RoundedModeP b radix P ->
 forall (p : R) (q : float), P p q -> (Rabs (p - q) < Fulp q)%R.
intros P H' p q H'0.
case (Req_dec p q); intros Eq1.
rewrite <- Eq1.
replace (p - p)%R with 0%R; [ idtac | ring ].
rewrite Rabs_R0; auto.
unfold Fulp, FtoRradix, FtoR in |- *; simpl in |- *; auto with real arith.
case H'.
intros H'1 H'2; elim H'2; intros H'3 H'4; elim H'4; intros H'5 H'6;
 case H'5 with (1 := H'0); clear H'5 H'4 H'2; intros H'5.
rewrite Rabs_right; auto.
cut (Fbounded b q); [ intros B0 | case H'5; auto ].
apply Rlt_le_trans with (2 := FulpSuc q B0).
apply Rplus_lt_reg_l with (r := FtoR radix q).
repeat rewrite Rplus_minus; auto.
case (Rle_or_lt (FNSucc b radix precision q) p); auto.
intros H'2; absurd (FNSucc b radix precision q <= q)%R; auto.
apply Rgt_not_le; red in |- *; unfold FtoRradix in |- *;
 auto with real float arith.
case H'5; auto.
intros H'4 H'7; elim H'7; intros H'8 H'9; apply H'9; clear H'7; auto.
apply (FcanonicBound radix b); auto with float arith.
apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix q).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; apply isMin_inv1 with (1 := H'5); auto.
rewrite Faux.Rabsolu_left1; auto.
rewrite Ropp_minus_distr; auto.
cut (Fbounded b q); [ intros B0 | case H'5; auto ].
apply Rlt_le_trans with (2 := FulpPred q B0).
apply Ropp_lt_cancel; repeat rewrite Rminus_0_l.
apply Rplus_lt_reg_l with (r := FtoR radix q).
repeat rewrite Rplus_minus; auto.
case (Rle_or_lt p (FNPred b radix precision q)); auto.
intros H'2; absurd (q <= FNPred b radix precision q)%R; auto.
apply Rgt_not_le; red in |- *; unfold FtoRradix in |- *;
 auto with real float arith.
case H'5; auto.
intros H'4 H'7; elim H'7; intros H'8 H'9; apply H'9; clear H'7; auto.
apply (FcanonicBound radix b); auto with float arith.
intros H1; apply Rplus_lt_compat_l; auto with real; apply Ropp_lt_contravar;
 unfold Rminus in |- *; auto with real.
apply Rplus_le_reg_l with (r := FtoR radix q).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; apply isMax_inv1 with (1 := H'5).
Qed.
 
Theorem RoundedModeErrorExpStrict :
 forall P,
 RoundedModeP b radix P ->
 forall (p q : float) (x : R),
 Fbounded b p ->
 Fbounded b q ->
 P x p -> q = (x - p)%R :>R -> q <> 0%R :>R -> (Fexp q < Fexp p)%Z.
intros P H p q x H0 H1 H2 H3 H4.
apply Zlt_powerRZ with (e := IZR radix); auto with real zarith.
apply Rle_lt_trans with (FtoRradix (Fabs q)).
replace (powerRZ radix (Fexp q)) with (FtoRradix (Float 1%nat (Fexp q)));
 unfold FtoRradix in |- *;
 [ apply Fop.RleFexpFabs; auto with arith
 | unfold FtoR in |- *; simpl in |- *; ring ].
rewrite (Fabs_correct radix); auto with zarith.
fold FtoRradix in |- *; rewrite H3.
apply Rlt_le_trans with (Fulp p);
 [ apply RoundedModeUlp with P; auto | unfold Fulp in |- * ].
apply Rle_powerRZ; auto with real zarith.
apply FcanonicLeastExp with radix b precision; auto with real arith.
apply sym_eq; apply FnormalizeCorrect; auto.
apply FnormalizeCanonic; auto with zarith.
Qed.
 
Theorem RoundedModeProjectorIdem :
 forall P (p : float), RoundedModeP b radix P -> Fbounded b p -> P p p.
intros P p H' H.
elim H'; intros H'0 H'1; elim H'1; intros H'2 H'3; elim H'3; intros H'4 H'5;
 clear H'3 H'1.
case (H'0 p).
intros x H'6.
apply (H'2 p p x); auto.
apply sym_eq; apply (RoundedProjector _ _ P H'); auto.
Qed.
 
Theorem RoundedModeBounded :
 forall P (r : R) (q : float),
 RoundedModeP b radix P -> P r q -> Fbounded b q.
intros P r q H' H'0.
case H'.
intros H'1 H'2; elim H'2; intros H'3 H'4; elim H'4; intros H'5 H'6;
 case H'5 with (1 := H'0); clear H'4 H'2; intros H; 
 case H; auto.
Qed.
 
Theorem RoundedModeProjectorIdemEq :
 forall (P : R -> float -> Prop) (p q : float),
 RoundedModeP b radix P -> Fbounded b p -> P (FtoR radix p) q -> p = q :>R.
intros P p q H' H'0 H'1.
cut (MinOrMaxP b radix P);
 [ intros Mn; case (Mn p q); auto; intros Mn1 | auto with inv ].
apply sym_eq; apply MinEq with (1 := Mn1); auto.
apply (RoundedModeProjectorIdem (isMin b radix)); auto.
apply MinRoundedModeP with (precision := precision); auto.
apply sym_eq; apply MaxEq with (1 := Mn1); auto.
apply (RoundedModeProjectorIdem (isMax b radix)); auto.
apply MaxRoundedModeP with (precision := precision); auto.
Qed.
 
Theorem RoundedModeMult :
 forall P,
 RoundedModeP b radix P ->
 forall (r : R) (q q' : float),
 P r q -> Fbounded b q' -> (r <= radix * q')%R -> (q <= radix * q')%R.
intros P H' r q q' H'0 H'1.
replace (radix * q')%R with (FtoRradix (Float (Fnum q') (Fexp q' + 1%nat))).
intros H'2; case H'2.
intros H'3; case H'; intros H'4 H'5; elim H'5; intros H'6 H'7; elim H'7;
 intros H'8 H'9; apply H'9 with (1 := H'3); clear H'7 H'5; 
 auto.
apply RoundedModeProjectorIdem; auto.
apply FBoundedScale; auto.
intros H'3.
replace (FtoRradix q) with (FtoRradix (Float (Fnum q') (Fexp q' + 1%nat)));
 auto with real.
apply (RoundedProjector _ _ P H'); auto.
apply FBoundedScale; auto.
case H'.
intros H'4 H'5; elim H'5; intros H'6 H'7; clear H'5.
apply (H'6 r (Float (Fnum q') (Fexp q' + 1%nat)) q); auto.
apply RoundedModeBounded with (P := P) (r := r); auto.
rewrite (FvalScale _ radixMoreThanOne b).
rewrite powerRZ_1; auto.
Qed.
 
Theorem RoundedModeMultLess :
 forall P,
 RoundedModeP b radix P ->
 forall (r : R) (q q' : float),
 P r q -> Fbounded b q' -> (radix * q' <= r)%R -> (radix * q' <= q)%R.
intros P H' r q q' H'0 H'1.
replace (radix * q')%R with (FtoRradix (Float (Fnum q') (Fexp q' + 1%nat))).
intros H'2; case H'2.
intros H'3; case H'; intros H'4 H'5; elim H'5; intros H'6 H'7; elim H'7;
 intros H'8 H'9; apply H'9 with (1 := H'3); clear H'7 H'5; 
 auto.
apply RoundedModeProjectorIdem; auto.
apply FBoundedScale; auto.
intros H'3.
replace (FtoRradix q) with (FtoRradix (Float (Fnum q') (Fexp q' + 1%nat)));
 auto with real.
apply (RoundedProjector _ _ P H'); auto.
apply FBoundedScale; auto.
unfold FtoRradix in H'3; rewrite H'3; auto.
case H'.
intros H'4 H'5; elim H'5; intros H'6 H'7; clear H'5.
unfold FtoRradix in |- *; rewrite FvalScale; auto.
rewrite powerRZ_1; auto.
Qed.
 
Theorem RleMinR0 :
 forall (r : R) (min : float),
 (0 <= r)%R -> isMin b radix r min -> (0 <= min)%R.
intros r min H' H'0.
rewrite <- (FzeroisZero radix b).
case H'; intros H'1.
apply (MonotoneMin b radix) with (p := FtoRradix (Fzero (- dExp b))) (q := r);
 auto.
unfold FtoRradix in |- *; rewrite (FzeroisZero radix b); auto.
apply (RoundedModeProjectorIdem (isMin b radix)); auto.
apply MinRoundedModeP with (precision := precision); auto with float.
apply FboundedFzero; auto.
replace (FtoR radix (Fzero (- dExp b))) with (FtoRradix min); auto with real.
apply sym_eq; apply (ProjectMin b radix).
apply FboundedFzero; auto.
rewrite <- H'1 in H'0; rewrite <- (FzeroisZero radix b) in H'0; auto.
Qed.
 
Theorem RleRoundedR0 :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P -> P r p -> (0 <= r)%R -> (0 <= p)%R.
intros P p r H' H'0 H'1.
case H'.
intros H'2 H'3; Elimc H'3; intros H'3 H'4; Elimc H'4; intros H'4 H'5;
 case (H'4 r p); auto; intros H'6.
apply RleMinR0 with (r := r); auto.
apply Rle_trans with r; auto; apply isMax_inv1 with (1 := H'6).
Qed.
 
Theorem RleMaxR0 :
 forall (r : R) (max : float),
 (r <= 0)%R -> isMax b radix r max -> (max <= 0)%R.
intros r max H' H'0.
rewrite <- (FzeroisZero radix b).
case H'; intros H'1.
apply (MonotoneMax b radix) with (q := FtoRradix (Fzero (- dExp b))) (p := r);
 auto.
unfold FtoRradix in |- *; rewrite FzeroisZero; auto.
apply (RoundedModeProjectorIdem (isMax b radix)); auto.
apply MaxRoundedModeP with (precision := precision); auto.
apply FboundedFzero; auto.
replace (FtoR radix (Fzero (- dExp b))) with (FtoRradix max); auto with real.
apply sym_eq; apply (ProjectMax b radix).
apply FboundedFzero; auto.
rewrite H'1 in H'0; rewrite <- (FzeroisZero radix b) in H'0; auto.
Qed.
 
Theorem RleRoundedLessR0 :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P -> P r p -> (r <= 0)%R -> (p <= 0)%R.
intros P p r H' H'0 H'1.
case H'.
intros H'2 H'3; Elimc H'3; intros H'3 H'4; Elimc H'4; intros H'4 H'5;
 case (H'4 r p); auto; intros H'6.
apply Rle_trans with r; auto; apply isMin_inv1 with (1 := H'6).
apply RleMaxR0 with (r := r); auto.
Qed.
 
Theorem PminPos :
 forall p min : float,
 (0 <= p)%R ->
 Fbounded b p ->
 isMin b radix (/ 2%nat * p) min ->
 exists c : float, Fbounded b c /\ c = (p - min)%R :>R.
intros p min H' H'0 H'1.
cut (min <= / 2%nat * p)%R;
 [ intros Rl1; Casec Rl1; intros Rl1
 | apply isMin_inv1 with (1 := H'1); auto ].
case (eqExpMax _ radixMoreThanOne b min p); auto.
case H'1; auto.
rewrite Fabs_correct; auto with arith.
rewrite Rabs_right; auto.
apply Rle_trans with (/ 2%nat * p)%R; auto.
apply Rlt_le; auto.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_ne_r;
 auto with real.
apply Rle_ge; apply RleMinR0 with (r := (/ 2%nat * p)%R); auto.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_1_l;
 rewrite Rmult_0_r; auto with real.
intros min' H'2; elim H'2; intros H'3 H'4; elim H'4; intros H'5 H'6;
 clear H'4 H'2.
case (FboundNext _ radixMoreThanOne b precision) with (p := min');
 auto with arith; fold FtoRradix in |- *.
intros Smin H'2; elim H'2; intros H'4 H'7; clear H'2.
exists Smin; split; auto.
rewrite H'7; auto.
unfold FtoRradix in |- *.
rewrite <- H'5; auto.
replace (Float (Zsucc (Fnum min')) (Fexp min')) with
 (Float (Fnum (Fshift radix (Zabs_nat (Fexp p - Fexp min')) p) - Fnum min')
    (Fexp min')); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite <- Z_R_minus.
rewrite (fun x y z : R => Rmult_comm (x - y) z); rewrite Rmult_minus_distr_l;
 repeat rewrite (fun x : Z => Rmult_comm (powerRZ radix x)).
rewrite Rmult_IZR.
rewrite Zpower_nat_powerRZ_absolu; auto with zarith.
rewrite Rmult_assoc.
rewrite <- (powerRZ_add radix); auto with real zarith.
replace (Fexp p - Fexp min' + Fexp min')%Z with (Fexp p); [ auto | ring ].
apply floatEq; auto; simpl in |- *.
apply Zle_antisym.
apply Zlt_succ_le.
apply Zplus_lt_reg_l with (p := Fnum min'); auto.
cut (forall x y : Z, (x + (y - x))%Z = y);
 [ intros tmp; rewrite tmp; clear tmp | intros; ring ].
replace (Fnum min' + Zsucc (Zsucc (Fnum min')))%Z with
 (2%nat * Zsucc (Fnum min'))%Z.
apply (Rlt_Float_Zlt radix) with (r := Fexp min'); auto;
 fold FtoRradix in |- *.
replace (FtoRradix (Float (2%nat * Zsucc (Fnum min')) (Fexp min'))) with
 (2%nat * Float (Zsucc (Fnum min')) (Fexp min'))%R.
rewrite <- H'7.
replace
 (Float (Fnum p * Zpower_nat radix (Zabs_nat (Fexp p - Fexp min')))
    (Fexp min')) with (Fshift radix (Zabs_nat (Fexp p - Fexp min')) p).
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto.
apply Rmult_lt_reg_l with (r := (/ 2%nat)%R); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real; rewrite Rmult_1_l;
 auto with real.
case (Rle_or_lt Smin (/ 2%nat * FtoR radix p)); auto.
intros H'2; absurd (min < Smin)%R.
apply Rle_not_lt.
case H'1; auto.
intros H'8 H'9; elim H'9; intros H'10 H'11; apply H'11; clear H'9; auto.
rewrite H'7; unfold FtoRradix in |- *; rewrite <- H'5; auto.
unfold FtoR in |- *; simpl in |- *; apply Rlt_monotony_exp;
 auto with real zarith.
unfold Fshift in |- *; simpl in |- *.
replace (Fexp p - Zabs_nat (Fexp p - Fexp min'))%Z with (Fexp min'); auto.
rewrite inj_abs; auto.
ring.
auto with zarith.
replace (FtoRradix (Float (2%nat * Zsucc (Fnum min')) (Fexp min'))) with
 ((2%nat * Zsucc (Fnum min'))%Z * powerRZ radix (Fexp min'))%R.
rewrite Rmult_IZR; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
simpl in |- *; auto.
replace (Z_of_nat 2) with (Zsucc (Zsucc 0)).
repeat rewrite <- Zmult_succ_l_reverse; unfold Zsucc in |- *; ring.
simpl in |- *; auto.
apply Zlt_le_succ; auto.
apply Zplus_lt_reg_l with (p := Fnum min'); auto.
cut (forall x y : Z, (x + (y - x))%Z = y);
 [ intros tmp; rewrite tmp; clear tmp | intros; ring ].
replace (Fnum min' + Fnum min')%Z with (2%nat * Fnum min')%Z.
apply (Rlt_Float_Zlt radix) with (r := Fexp min'); auto;
 fold FtoRradix in |- *.
replace (FtoRradix (Float (2%nat * Fnum min') (Fexp min'))) with
 (2%nat * Float (Fnum min') (Fexp min'))%R.
replace
 (Float (Fnum p * Zpower_nat radix (Zabs_nat (Fexp p - Fexp min')))
    (Fexp min')) with (Fshift radix (Zabs_nat (Fexp p - Fexp min')) p).
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto.
apply Rmult_lt_reg_l with (r := (/ 2%nat)%R); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real; rewrite Rmult_1_l;
 auto with real.
replace (FtoR radix (Float (Fnum min') (Fexp min'))) with (FtoR radix min);
 auto.
unfold Fshift in |- *; simpl in |- *.
replace (Fexp p - Zabs_nat (Fexp p - Fexp min'))%Z with (Fexp min'); auto.
rewrite inj_abs; auto.
ring.
auto with zarith.
replace (FtoRradix (Float (2%nat * Fnum min') (Fexp min'))) with
 ((2%nat * Fnum min')%Z * powerRZ radix (Fexp min'))%R.
rewrite Rmult_IZR; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
simpl in |- *; auto.
replace (Z_of_nat 2) with (Zsucc (Zsucc 0)).
repeat rewrite <- Zmult_succ_l_reverse; unfold Zsucc in |- *; ring.
simpl in |- *; auto.
exists min; split; auto.
case H'1; auto.
rewrite Rl1.
pattern (FtoRradix p) at 2 in |- *;
 replace (FtoRradix p) with (2%nat * (/ 2%nat * p))%R.
simpl in |- *; ring.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_ne_r;
 auto with real.
Qed.
 
Theorem div2IsBetweenPos :
 forall p min max : float,
 (0 <= p)%R ->
 Fbounded b p ->
 isMin b radix (/ 2%nat * p) min ->
 isMax b radix (/ 2%nat * p) max -> p = (min + max)%R :>R.
intros p min max P H' H'0 H'1; apply Rle_antisym.
apply Rplus_le_reg_l with (r := (- max)%R).
replace (- max + p)%R with (p - max)%R; [ idtac | ring ].
replace (- max + (min + max))%R with (FtoRradix min); [ idtac | ring ].
rewrite <- (Fminus_correct radix); auto with arith.
case H'0.
intros H'2 H'3; elim H'3; intros H'4 H'5; apply H'5; clear H'3; auto.
apply Sterbenz; auto.
case H'1; auto.
apply Rle_trans with (FtoRradix max); auto.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_1_l;
 auto with real.
apply Rledouble; auto.
apply Rle_trans with (FtoRradix min); auto.
apply RleMinR0 with (r := (/ 2%nat * p)%R); auto.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_1_l;
 rewrite Rmult_0_r; auto with real.
apply Rle_trans with (/ 2%nat * p)%R; auto; apply isMax_inv1 with (1 := H'1).
case H'1.
intros H'3 H'6; elim H'6; intros H'7 H'8; apply H'8; clear H'6; auto.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_1_l;
 auto with real.
apply Rmult_le_reg_l with (r := (/ 2%nat)%R); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real; rewrite Rmult_1_l;
 auto with real.
apply isMax_inv1 with (1 := H'1).
rewrite Fminus_correct; auto with arith.
apply Rplus_le_reg_l with (r := FtoR radix max).
replace (FtoR radix max + (FtoR radix p - FtoR radix max))%R with
 (FtoR radix p); [ idtac | ring ].
apply Rplus_le_reg_l with (r := (- (/ 2%nat * p))%R).
replace (- (/ 2%nat * p) + FtoR radix p)%R with (/ 2%nat * p)%R.
replace (- (/ 2%nat * p) + (FtoR radix max + / 2%nat * p))%R with
 (FtoR radix max); [ apply isMax_inv1 with (1 := H'1) | ring ].
replace (FtoR radix p) with (2%nat * (/ 2%nat * p))%R.
simpl in |- *; ring.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real.
apply Rplus_le_reg_l with (r := (- min)%R).
replace (- min + p)%R with (p - min)%R; [ idtac | ring ].
replace (- min + (min + max))%R with (FtoRradix max); [ idtac | ring ].
case (PminPos p min); auto.
intros x H'2; elim H'2; intros H'3 H'4; elim H'4; clear H'2.
case H'1.
intros H'2 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
unfold FtoRradix in H'4; rewrite H'4; auto.
fold FtoRradix in |- *; apply Rplus_le_reg_l with (r := FtoRradix min).
replace (min + (p - min))%R with (FtoRradix p); [ idtac | ring ].
apply Rplus_le_reg_l with (r := (- (/ 2%nat * p))%R).
replace (- (/ 2%nat * p) + p)%R with (/ 2%nat * p)%R.
replace (- (/ 2%nat * p) + (min + / 2%nat * p))%R with (FtoRradix min);
 [ apply isMin_inv1 with (1 := H'0) | ring ].
pattern (FtoRradix p) at 3 in |- *;
 replace (FtoRradix p) with (2%nat * (/ 2%nat * p))%R.
simpl in |- *; ring.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real.
Qed.
 
Theorem div2IsBetween :
 forall p min max : float,
 Fbounded b p ->
 isMin b radix (/ 2%nat * p) min ->
 isMax b radix (/ 2%nat * p) max -> p = (min + max)%R :>R.
intros p min max H' H'0 H'1; case (Rle_or_lt 0 p); intros H'2.
apply div2IsBetweenPos; auto.
cut (forall x y : R, (- x)%R = (- y)%R -> x = y);
 [ intros H'3; apply H'3; clear H'3 | idtac ].
replace (- (min + max))%R with (- max + - min)%R; [ idtac | ring ].
repeat rewrite <- (Fopp_correct radix); auto with float.
apply div2IsBetweenPos; auto with float.
rewrite (Fopp_correct radix); auto.
replace 0%R with (-0)%R; try apply Rlt_le; auto with real.
replace (/ 2%nat * Fopp p)%R with (- (/ 2%nat * p))%R; auto with float.
rewrite (Fopp_correct radix); auto; fold FtoRradix; ring.
replace (/ 2%nat * Fopp p)%R with (- (/ 2%nat * p))%R; auto with float.
rewrite (Fopp_correct radix); auto; fold FtoRradix;ring.
intros x y H'3; rewrite <- (Ropp_involutive x);
 rewrite <- (Ropp_involutive y); rewrite H'3; auto.
Qed.
 
Theorem RoundedModeMultAbs :
 forall P,
 RoundedModeP b radix P ->
 forall (r : R) (q q' : float),
 P r q ->
 Fbounded b q' -> (Rabs r <= radix * q')%R -> (Rabs q <= radix * q')%R.
intros P H' r q q' H'0 H'1 H'2.
case (Rle_or_lt 0 r); intros Rl0.
rewrite Rabs_right; auto.
apply RoundedModeMult with (P := P) (r := r); auto.
rewrite <- (Rabs_right r); auto with real.
apply Rle_ge; apply RleRoundedR0 with (P := P) (r := r); auto.
rewrite Faux.Rabsolu_left1; auto.
replace (radix * q')%R with (- (radix * - q'))%R;
 [ apply Ropp_le_contravar | ring ].
rewrite <- (Fopp_correct radix).
apply RoundedModeMultLess with (P := P) (r := r); auto.
apply oppBounded; auto.
unfold FtoRradix in |- *; rewrite Fopp_correct.
rewrite <- (Ropp_involutive r).
replace (radix * - FtoR radix q')%R with (- (radix * q'))%R;
 [ apply Ropp_le_contravar | fold FtoRradix;ring ]; auto.
rewrite <- (Faux.Rabsolu_left1 r); auto.
apply Rlt_le; auto.
apply RleRoundedLessR0 with (P := P) (r := r); auto.
apply Rlt_le; auto.
Qed.
 
Theorem isMinComp :
 forall (r1 r2 : R) (min max : float),
 isMin b radix r1 min ->
 isMax b radix r1 max -> (min < r2)%R -> (r2 < max)%R -> isMin b radix r2 min.
intros r1 r2 min max H' H'0 H'1 H'2; split.
case H'; auto.
split.
apply Rlt_le; auto.
intros f H'3 H'4.
case H'; auto.
intros H'5 H'6; elim H'6; intros H'7 H'8; apply H'8; clear H'6; auto.
case (Rle_or_lt (FtoR radix f) r1); auto; intros C1.
absurd (FtoR radix f < max)%R.
apply Rle_not_lt.
case H'0.
intros H'6 H'9; elim H'9; intros H'10 H'11; apply H'11; clear H'9; auto.
apply Rlt_le; auto.
apply Rle_lt_trans with (2 := H'2); auto.
Qed.
 
Theorem isMaxComp :
 forall (r1 r2 : R) (min max : float),
 isMin b radix r1 min ->
 isMax b radix r1 max -> (min < r2)%R -> (r2 < max)%R -> isMax b radix r2 max.
intros r1 r2 min max H' H'0 H'1 H'2; split.
case H'0; auto.
split.
apply Rlt_le; auto.
intros f H'3 H'4.
case H'0; auto.
intros H'5 H'6; elim H'6; intros H'7 H'8; apply H'8; clear H'6; auto.
case (Rle_or_lt r1 (FtoR radix f)); auto; intros C1.
absurd (min < FtoR radix f)%R.
apply Rle_not_lt.
case H'.
intros H'6 H'9; elim H'9; intros H'10 H'11; apply H'11; clear H'9; auto.
apply Rlt_le; auto.
apply Rlt_le_trans with (1 := H'1); auto.
Qed.
 
Theorem roundedModeLessMult :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P ->
 P r p -> (Float 1%nat (- dExp b) <= r)%R -> (p <= radix * r)%R.
intros P p r H' H'0 H'1.
cut (0 < Float 1%nat (- dExp b))%R;
 [ intros Rl0
 | unfold FtoRradix, FtoR in |- *; simpl in |- *; rewrite Rmult_1_l;
    auto with real arith ].
cut (0 < r)%R; [ intros Rl1 | apply Rlt_le_trans with (1 := Rl0) ]; auto.
cut (0 <= r)%R; [ intros Rl2 | apply Rlt_le; auto ].
case H'.
intros H'2 H'3; Elimc H'3; intros H'3 H'4; Elimc H'4; intros H'4 H'5;
 case (H'4 r p); auto; intros H'6.
apply Rle_trans with r; auto with real.
apply isMin_inv1 with (1 := H'6).
rewrite Rmult_comm; pattern r at 1 in |- *; replace r with (r * 1%nat)%R;
 [ apply Rmult_le_compat_l | simpl; ring ]; auto with real arith.
case (MinEx b radix precision) with (r := r); auto with arith;
 intros min Hmin.
cut (Fbounded b (Float (Fnum min) (Zsucc (Fexp min)))); [ intros F2 | idtac ].
cut (FtoRradix (Float (Fnum min) (Zsucc (Fexp min))) = (radix * min)%R :>R);
 [ intros F2Eq | idtac ].
apply Rle_trans with (FtoRradix (Float (Fnum min) (Zsucc (Fexp min)))).
case H'6.
intros H'7 H'8; elim H'8; intros H'9 H'10; apply H'10; clear H'8; auto.
case (Rle_or_lt r (Float (Fnum min) (Zsucc (Fexp min)))); auto; intros Rlt0.
absurd (Float (Fnum min) (Zsucc (Fexp min)) <= min)%R.
apply Rgt_not_le.
rewrite F2Eq; auto with real.
rewrite Rmult_comm.
pattern (FtoRradix min) at 2 in |- *;
 replace (FtoRradix min) with (min * 1%nat)%R; auto with real.
red in |- *; apply Rmult_lt_compat_l; auto with real arith.
case (RleMinR0 r min); auto.
intros H'8; case H'1.
intros H'11; absurd (Float 1%nat (- dExp b) <= min)%R.
apply Rgt_not_le; auto.
rewrite <- H'8; auto.
apply
 (MonotoneMin b radix)
  with (p := FtoRradix (Float 1%nat (- dExp b))) (q := r); 
 auto.
apply (RoundedModeProjectorIdem (isMin b radix)); auto.
apply MinRoundedModeP with (precision := precision); auto.
repeat split.
simpl in |- *; auto with zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
simpl in |- *; auto with zarith.
intros H'11; absurd (min = Float 1%nat (- dExp b) :>R).
rewrite <- H'8.
apply Rlt_dichotomy_converse; left; auto.
apply (MinUniqueP b radix r); auto.
rewrite <- H'11.
apply (RoundedModeProjectorIdem (isMin b radix)); auto.
apply MinRoundedModeP with (precision := precision); auto.
repeat split.
simpl in |- *; auto with zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
simpl in |- *; auto with zarith.
case Hmin.
intros H'8 H'11; elim H'11; intros H'12 H'13; apply H'13; clear H'11; auto.
apply Rlt_le; auto.
rewrite F2Eq.
apply Rmult_le_compat_l; auto with real arith.
replace 0%R with (INR 0); auto with real arith.
apply isMin_inv1 with (1 := Hmin).
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; ring.
cut (Fbounded b min);
 [ unfold Fbounded in |- *; intros Fb0 | case Hmin; auto ].
elim Fb0; intros H H0; auto.
repeat (split; simpl in |- *); auto.
apply Zle_trans with (Fexp min); auto with zarith.
Qed.
 
Theorem roundedModeMoreMult :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P ->
 P r p -> (r <= Float (- 1%nat) (- dExp b))%R -> (radix * r <= p)%R.
intros P p r H' H'0 H'1.
cut (Float (- 1%nat) (- dExp b) < 0)%R;
 [ intros Rl0
 | unfold FtoRradix, FtoR in |- *; simpl in |- *; unfold IZR at 1; rewrite Ropp_mult_distr_l_reverse;
   rewrite Rmult_1_l;
    auto with real arith ].
2: replace 0%R with (-0)%R; auto with real arith; ring.
cut (r < 0)%R; [ intros Rl1 | apply Rle_lt_trans with (2 := Rl0) ]; auto.
cut (r <= 0)%R; [ intros Rl2 | apply Rlt_le; auto ].
case H'.
intros H'2 H'3; Elimc H'3; intros H'3 H'4; Elimc H'4; intros H'4 H'5;
 case (H'4 r p); auto; intros H'6.
case (MaxEx b radix precision) with (r := r); auto with arith;
 intros max Hmax.
cut (Fbounded b (Float (Fnum max) (Zsucc (Fexp max)))); [ intros F2 | idtac ].
cut (FtoRradix (Float (Fnum max) (Zsucc (Fexp max))) = (radix * max)%R :>R);
 [ intros F2Eq | idtac ].
apply Rle_trans with (FtoRradix (Float (Fnum max) (Zsucc (Fexp max)))).
rewrite F2Eq; auto with real.
apply Rmult_le_compat_l; auto with real arith.
replace 0%R with (INR 0); auto with real arith.
apply isMax_inv1 with (1 := Hmax); auto.
case H'6.
intros H'7 H'8; elim H'8; intros H'9 H'10; apply H'10; clear H'8; auto.
case (Rle_or_lt (Float (Fnum max) (Zsucc (Fexp max))) r); auto; intros Rlt0.
absurd (max <= Float (Fnum max) (Zsucc (Fexp max)))%R.
apply Rgt_not_le.
rewrite F2Eq.
replace (radix * max)%R with (- (- max * radix))%R; [ idtac | ring ].
pattern (FtoRradix max) at 1 in |- *;
 replace (FtoRradix max) with (- (- max * 1%nat))%R;
 [ idtac | simpl in |- *; ring ].
apply Ropp_lt_gt_contravar; apply Rmult_lt_compat_l; auto with real.
replace 0%R with (-0)%R; [ apply Ropp_lt_contravar | ring ].
case (RleMaxR0 r max); auto.
intros H'8; case H'1.
intros H'11; absurd (max <= Float (- 1%nat) (- dExp b))%R.
apply Rgt_not_le; auto.
rewrite H'8; auto.
apply
 (MonotoneMax b radix)
  with (q := FtoRradix (Float (- 1%nat) (- dExp b))) (p := r); 
 auto.
apply (RoundedModeProjectorIdem (isMax b radix)); auto.
apply MaxRoundedModeP with (precision := precision); auto.
repeat split.
simpl in |- *; auto with zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
simpl in |- *; auto with zarith.
intros H'11; absurd (Float (- 1%nat) (- dExp b) = max :>R).
rewrite H'8; auto.
apply Rlt_dichotomy_converse; left; auto.
apply (MaxUniqueP b radix r); auto.
rewrite H'11.
apply (RoundedModeProjectorIdem (isMax b radix)); auto.
apply MaxRoundedModeP with (precision := precision); auto.
repeat split.
simpl in |- *; auto with zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
simpl in |- *; auto with zarith.
case Hmax.
intros H'8 H'11; elim H'11; intros H'12 H'13; apply H'13; clear H'11; auto.
apply Rlt_le; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; ring.
cut (Fbounded b max);
 [ unfold Fbounded in |- *; intros Fb0 | case Hmax; auto ].
elim Fb0; intros H H0; repeat (split; simpl in |- *); auto.
apply Zle_trans with (Fexp max); auto with zarith.
apply Rle_trans with r; auto with real.
pattern r at 2 in |- *; replace r with (- (- r * 1%nat))%R; [ idtac | simpl; ring ].
replace (radix * r)%R with (- (- r * radix))%R; [ idtac | ring ].
apply Ropp_le_contravar; apply Rmult_le_compat_l; auto with real arith.
replace 0%R with (-0)%R; auto with real arith.
apply isMax_inv1 with (1 := H'6).
Qed.
 
Theorem roundedModeAbsMult :
 forall (P : R -> float -> Prop) (p : float) (r : R),
 RoundedModeP b radix P ->
 P r p ->
 (Float 1%nat (- dExp b) <= Rabs r)%R -> (Rabs p <= radix * Rabs r)%R.
intros P p r H' H'0 H'1; case (Rle_or_lt 0 r); intros H'2.
repeat rewrite Rabs_right; auto with real.
apply roundedModeLessMult with (P := P); auto.
rewrite <- (Rabs_right r); auto with real.
apply Rle_ge; apply (RleRoundedR0 P) with (r := r); auto.
repeat rewrite Faux.Rabsolu_left1; auto.
replace (radix * - r)%R with (- (radix * r))%R;
 [ apply Ropp_le_contravar | ring ].
apply roundedModeMoreMult with (P := P); auto.
rewrite <- (Ropp_involutive r); rewrite <- (Faux.Rabsolu_left1 r); auto.
replace (Float (- 1%nat) (- dExp b)) with (Fopp (Float 1%nat (- dExp b))).
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
simpl in |- *; auto.
apply Rlt_le; auto.
apply Rlt_le; auto.
apply (RleRoundedLessR0 P) with (r := r); auto.
apply Rlt_le; auto.
Qed.
 
Theorem RleBoundRoundl :
 forall P,
 RoundedModeP b radix P ->
 forall (p q : float) (r : R),
 Fbounded b p -> (p <= r)%R -> P r q -> (p <= q)%R.
intros P H' p q r H'0 H'1 H'2; case H'1; intros H'3.
cut (MonotoneP radix P);
 [ intros Mn | apply RoundedModeP_inv4 with (1 := H'); auto ].
apply (Mn p r); auto.
apply RoundedModeProjectorIdem with (P := P); auto.
rewrite RoundedModeProjectorIdemEq with (P := P) (p := p) (q := q);
 auto with real.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := H'); auto ].
apply (Cp r p q); auto.
apply RoundedModeBounded with (P := P) (r := r); auto.
Qed.
 
Theorem RleBoundRoundr :
 forall P,
 RoundedModeP b radix P ->
 forall (p q : float) (r : R),
 Fbounded b p -> (r <= p)%R -> P r q -> (q <= p)%R.
intros P H' p q r H'0 H'1 H'2; case H'1; intros H'3.
cut (MonotoneP radix P);
 [ intros Mn | apply RoundedModeP_inv4 with (1 := H'); auto ].
apply (Mn r p); auto.
apply RoundedModeProjectorIdem with (P := P); auto.
rewrite RoundedModeProjectorIdemEq with (P := P) (p := p) (q := q);
 auto with real.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := H'); auto ].
apply (Cp r p q); auto.
apply RoundedModeBounded with (P := P) (r := r); auto.
Qed.
 
Theorem RoundAbsMonotoner :
 forall (P : R -> float -> Prop) (p : R) (q r : float),
 RoundedModeP b radix P ->
 Fbounded b r -> P p q -> (Rabs p <= r)%R -> (Rabs q <= r)%R.
intros P p q r H' H'0 H'1 H'2.
case (Rle_or_lt 0 p); intros Rl1.
rewrite Rabs_right; auto with real.
apply RleBoundRoundr with (P := P) (r := p); auto with real.
rewrite <- (Rabs_right p); auto with real.
apply Rle_ge; apply RleRoundedR0 with (P := P) (r := p); auto.
rewrite Faux.Rabsolu_left1; auto.
rewrite <- (Ropp_involutive r); apply Ropp_le_contravar.
rewrite <- (Fopp_correct radix); auto.
apply RleBoundRoundl with (P := P) (r := p); auto with float.
rewrite (Fopp_correct radix); rewrite <- (Ropp_involutive p);
 rewrite <- (Faux.Rabsolu_left1 p); auto with real; 
 apply Rlt_le; auto.
apply RleRoundedLessR0 with (P := P) (r := p); auto; apply Rlt_le; auto.
Qed.
 
Theorem RoundAbsMonotonel :
 forall (P : R -> float -> Prop) (p : R) (q r : float),
 RoundedModeP b radix P ->
 Fbounded b r -> P p q -> (r <= Rabs p)%R -> (r <= Rabs q)%R.
intros P p q r H' H'0 H'1 H'2.
case (Rle_or_lt 0 p); intros Rl1.
rewrite Rabs_right; auto.
apply RleBoundRoundl with (P := P) (r := p); auto.
rewrite <- (Rabs_right p); auto with real.
apply Rle_ge; apply RleRoundedR0 with (P := P) (r := p); auto.
rewrite Faux.Rabsolu_left1; auto.
rewrite <- (Ropp_involutive r); apply Ropp_le_contravar.
rewrite <- (Fopp_correct radix); auto.
apply RleBoundRoundr with (P := P) (r := p); auto with float.
rewrite (Fopp_correct radix); rewrite <- (Ropp_involutive p);
 rewrite <- (Faux.Rabsolu_left1 p); auto with real; 
 apply Rlt_le; auto.
apply RleRoundedLessR0 with (P := P) (r := p); auto; apply Rlt_le; auto.
Qed.
(* Rounded of natural numbers are natural *)
 
Theorem ZroundZ :
 forall (P : R -> float -> Prop) (z : Z) (p : float),
 RoundedModeP b radix P -> P z p -> exists z' : Z, p = z' :>R.
intros P z p HP H'.
case
 (RoundedModeRep b radix precision)
  with (P := P) (p := Float z 0%nat) (q := p); auto.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := HP); auto ]; 
 auto.
apply Cp with (1 := H'); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Rmult_1_r; auto.
apply RoundedModeBounded with (P := P) (r := IZR z); auto.
intros x H'0; exists x; auto.
unfold FtoRradix in |- *; rewrite H'0.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Rmult_1_r; auto.
Qed.
 
Theorem NroundN :
 forall (P : R -> float -> Prop) (n : nat) (p : float),
 RoundedModeP b radix P -> P n p -> exists n' : nat, p = n' :>R.
intros P n p HP H'.
case (ZroundZ P (Z_of_nat n) p); auto.
repeat rewrite <- INR_IZR_INZ; auto.
intros x H'0; exists (Zabs_nat x).
rewrite <- (inj_abs x) in H'0.
rewrite H'0.
repeat rewrite <- INR_IZR_INZ; auto.
apply le_IZR; simpl in |- *.
rewrite <- H'0; auto.
apply RleRoundedR0 with (P := P) (r := INR n); auto.
replace 0%R with (INR 0); auto with real arith.
Qed.
(* Properties of LSB and MSB *)
 
Theorem FUlp_Le_LSigB :
 forall x : float, Fbounded b x -> (Fulp x <= Float 1%nat (LSB radix x))%R.
intros x H; unfold is_Fzero, Fulp, Fnormalize in |- *;
 case (Z_zerop (Fnum x)); intros ZH.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Rmult_1_l.
apply Rle_powerRZ.
replace 1%R with (INR 1); auto with real arith.
apply Zle_trans with (Fexp x); auto.
case H; auto.
apply Fexp_le_LSB; auto.
rewrite
 LSB_shift
           with
           (n := 
             min (precision - Fdigit radix x) (Zabs_nat (dExp b + Fexp x)));
 auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Rmult_1_l.
apply Rle_powerRZ; auto with arith.
replace 1%R with (INR 1); auto with real arith.
exact
 (Fexp_le_LSB radix
    (Fshift radix
       (min (precision - Fdigit radix x) (Zabs_nat (dExp b + Fexp x))) x)).
Qed.
 
Theorem MSBisMin :
 forall f1 f2 : float,
 (0 <= f1)%R ->
 isMin b radix f1 f2 ->
 ~ is_Fzero f1 -> ~ is_Fzero f2 -> MSB radix f1 = MSB radix f2.
intros f1 f2 H' H'0 H'1 H'2.
apply Zle_antisym.
2: apply MSB_monotone; auto.
2: repeat rewrite Fabs_correct1; auto with arith.
2: apply isMin_inv1 with (1 := H'0).
2: apply RleRoundedR0 with (P := isMin b radix) (r := FtoRradix f1); auto.
2: apply MinRoundedModeP with (precision := precision); auto.
case (Zle_or_lt (MSB radix f1) (MSB radix f2)); auto.
intros H'3; absurd (Float 1%nat (Zsucc (MSB radix f2)) <= f2)%R.
apply Rgt_not_le.
red in |- *; unfold FtoRradix in |- *; rewrite <- Fabs_correct1;
 auto with float arith.
apply abs_lt_MSB; auto.
apply RleRoundedR0 with (P := isMin b radix) (r := FtoRradix f1);
 auto with float.
apply MinRoundedModeP with (precision := precision); auto.
case H'0.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply (FboundedOne _ radixMoreThanOne b precision); auto with arith.
apply Zle_trans with (Fexp f2).
case H'4; auto.
apply Zle_trans with (MSB radix f2); auto with zarith.
apply Fexp_le_MSB; auto.
apply Rle_trans with (FtoR radix (Float 1%nat (MSB radix f1))); auto.
apply oneExp_le; auto with zarith.
unfold FtoRradix in |- *; rewrite <- Fabs_correct1 with (x := f1);
 auto with float arith.
apply MSB_le_abs; auto.
Qed.
 
Theorem MSBtoZero :
 forall f1 f2 : float,
 ToZeroP b radix f1 f2 ->
 ~ is_Fzero f1 -> ~ is_Fzero f2 -> MSB radix f1 = MSB radix f2.
intros f1 f2 H' H'0 H'1; Casec H'; intros tmp; Elimc tmp; intros H1 H2.
apply MSBisMin; auto.
rewrite (MSB_opp radix f1).
rewrite (MSB_opp radix f2).
apply MSBisMin; auto with float.
unfold FtoRradix in |- *; rewrite Fopp_correct.
replace 0%R with (-0)%R; auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with float.
Qed.
 
Theorem MSBBoundNotZero :
 forall P : R -> float -> Prop,
 RoundedModeP b radix P ->
 forall f1 f2 : float,
 P f1 f2 -> f1 <> 0%R :>R -> (- dExp b <= MSB radix f1)%Z -> f2 <> 0%R :>R.
intros P H' f1 f2 H'0 H'1 H'2.
case (Rle_or_lt 0 f1); intros Rl1.
apply Rlt_dichotomy_converse; right; red in |- *.
apply Rlt_le_trans with (r2 := FtoRradix (Float 1%nat (MSB radix f1))); auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; rewrite Rmult_1_l;
 auto with real arith.
cut (Float 1%nat (MSB radix f1) <= Fabs f1)%R; unfold FtoRradix in |- *;
 [ rewrite Fabs_correct; auto with arith; rewrite Rabs_right; auto with real;
    intros Rl2; Casec Rl2; intros Rl2
 | apply MSB_le_abs ]; auto.
cut (MonotoneP radix P);
 [ intros Mn | apply RoundedModeP_inv4 with (1 := H'); auto ].
apply (Mn (Float 1%nat (MSB radix f1)) f1); auto.
apply RoundedModeProjectorIdem; auto.
apply (FboundedOne radix) with (precision := precision);
 auto with real zarith arith.
replace (FtoR radix f2) with (FtoR radix (Float 1%nat (MSB radix f1)));
 auto with float real.
apply RoundedModeProjectorIdemEq with (P := P); auto.
apply (FboundedOne radix) with (precision := precision);
 auto with real zarith arith.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := H'); auto ].
apply (Cp f1) with (p := f2); auto.
apply RoundedModeBounded with (P := P) (r := FtoRradix f1); auto.
Contradict H'1; unfold FtoRradix in |- *; apply is_Fzero_rep1; auto.
apply Rlt_dichotomy_converse; left.
apply Rle_lt_trans with (r2 := FtoRradix (Float (- 1%nat) (MSB radix f1)));
 auto.
cut (MonotoneP radix P);
 [ intros Mn | apply RoundedModeP_inv4 with (1 := H'); auto ].
cut (f1 <= Float (- 1%nat) (MSB radix f1))%R;
 [ intros Rle1; Casec Rle1; intros Rle1 | idtac ].
apply (Mn f1 (Float (- 1%nat) (MSB radix f1))); auto.
apply RoundedModeProjectorIdem; auto.
apply oppBoundedInv; unfold Fopp in |- *; simpl in |- *.
apply (FboundedOne radix) with (precision := precision);
 auto with real zarith arith.
replace (FtoRradix f2) with (FtoRradix (Float (- 1%nat) (MSB radix f1)));
 auto with real.
apply RoundedModeProjectorIdemEq with (P := P); auto.
apply oppBoundedInv; unfold Fopp in |- *; simpl in |- *.
apply (FboundedOne _ radixMoreThanOne b precision);
 auto with real zarith arith.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := H'); auto ].
apply (Cp f1) with (p := f2); auto.
apply RoundedModeBounded with (P := P) (r := FtoRradix f1); auto.
replace (FtoRradix f1) with (- FtoRradix (Fabs f1))%R.
replace (Float (- 1%nat) (MSB radix f1)) with
 (Fopp (Float 1%nat (MSB radix f1))).
unfold FtoRradix in |- *; rewrite Fopp_correct; auto.
apply Ropp_le_contravar; apply MSB_le_abs; auto.
Contradict H'1; unfold FtoRradix in |- *; apply is_Fzero_rep1; auto.
unfold Fopp in |- *; simpl in |- *; auto.
unfold FtoRradix in |- *; rewrite Fabs_correct; auto with arith;
 rewrite Faux.Rabsolu_left1; try apply Rlt_le; auto; 
 ring.
replace (Float (- 1%nat) (MSB radix f1)) with
 (Fopp (Float 1%nat (MSB radix f1)));
 [ idtac | unfold Fopp in |- *; simpl in |- *; auto ].
replace 0%R with (-0)%R; [ idtac | ring ].
unfold FtoRradix in |- *; repeat rewrite Fopp_correct;
 apply Ropp_lt_contravar.
unfold FtoR in |- *; simpl in |- *; rewrite Rmult_1_l; auto with real arith.
Qed.
 
Theorem RoundMSBmax :
 forall (P : R -> float -> Prop) (p q : float),
 RoundedModeP b radix P ->
 P p q ->
 p <> 0%R :>R ->
 (- dExp b <= MSB radix p)%Z -> (MSB radix q <= Zsucc (MSB radix p))%Z.
intros P p q H' H'0 H'1 H'2.
apply (oneExp_Zle radix); auto.
apply Rle_trans with (FtoRradix (Fabs q)).
unfold FtoRradix in |- *; apply MSB_le_abs; auto.
red in |- *; intros H'3; absurd (q = 0%R :>R).
apply MSBBoundNotZero with (P := P) (f1 := p); auto.
apply (is_Fzero_rep1 radix); auto.
unfold FtoRradix in |- *; rewrite Fabs_correct; auto with arith;
 fold FtoRradix in |- *.
apply RoundAbsMonotoner with (P := P) (p := FtoRradix p); auto.
apply (FboundedOne _ radixMoreThanOne b precision); auto with zarith.
unfold FtoRradix in |- *; rewrite <- (Fabs_correct radix); auto with arith.
apply Rlt_le; apply abs_lt_MSB; auto.
Qed.
 
Theorem RoundMSBmin :
 forall (P : R -> float -> Prop) (p q : float),
 RoundedModeP b radix P ->
 P p q ->
 p <> 0%R :>R ->
 (- dExp b <= MSB radix p)%Z -> (MSB radix p <= MSB radix q)%Z.
intros P p q H' H'0 H'1 H'2.
replace (MSB radix p) with (MSB radix (Float 1%nat (MSB radix p))).
apply MSB_monotone; auto.
unfold is_Fzero in |- *; simpl in |- *; red in |- *; intros; discriminate.
red in |- *; intros H'3; absurd (q = 0%R :>R).
apply MSBBoundNotZero with (P := P) (f1 := p); auto.
unfold FtoRradix in |- *; apply is_Fzero_rep1; auto.
replace (Fabs (Float 1%nat (MSB radix p))) with (Float 1%nat (MSB radix p));
 [ idtac | unfold Fabs in |- *; simpl in |- *; auto ].
rewrite Fabs_correct; auto with arith; fold FtoRradix in |- *.
apply RoundAbsMonotonel with (P := P) (p := FtoRradix p); auto.
apply (FboundedOne _ radixMoreThanOne b precision); auto with zarith.
unfold FtoRradix in |- *; rewrite <- (Fabs_correct radix); auto with arith;
 apply MSB_le_abs; auto.
Contradict H'1; unfold FtoRradix in |- *; apply is_Fzero_rep1; auto.
unfold MSB, Fdigit in |- *; simpl in |- *.
case (Zpred (digit radix (Fnum p) + Fexp p)); simpl in |- *; auto with zarith.
intros p0; case p0; simpl in |- *; auto.
intros p1; elim p1; simpl in |- *; auto.
intros p2 H; injection H; intros H1; rewrite <- H1; auto.
intros p0; case p0; simpl in |- *; auto.
intros p1; case p1; simpl in |- *; auto.
intros p2; elim p2; simpl in |- *; auto.
intros p3 H; injection H; intros H1; rewrite H1; auto.
Qed.
 
Theorem RoundLSBMax :
 forall (P : R -> float -> Prop) (p q : float),
 RoundedModeP b radix P ->
 P p q -> ~ is_Fzero q -> (LSB radix p <= LSB radix q)%Z.
intros P p q H' H'0 H'2.
elim (LSB_rep_min radix) with (p := p); auto; intros z E.
case
 (RoundedModeRep b radix precision)
  with (P := P) (p := Float z (LSB radix p)) (q := q); 
 auto.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := H'); auto ].
apply (Cp p (Float z (LSB radix p)) q); auto.
apply RoundedModeBounded with (P := P) (r := FtoRradix p); auto.
intros x H'3.
replace (LSB radix p) with (Fexp (Float x (LSB radix p)));
 [ idtac | simpl in |- *; auto ].
replace (LSB radix q) with (LSB radix (Float x (LSB radix p))).
apply Fexp_le_LSB.
apply LSB_comp; auto.
apply NisFzeroComp with (radix := radix) (x := q); auto.
Qed.
(* General theorem about the binade *)
 
Theorem InBinade :
 forall (P : R -> float -> Prop) (p q r : float) (e : Z),
 RoundedModeP b radix P ->
 Fbounded b p ->
 Fbounded b q ->
 P (p + q)%R r ->
 (- dExp b <= e)%Z ->
 (Float (Zpower_nat radix (pred precision)) e <= p)%R ->
 (p <= Float (pPred (vNum b)) e)%R ->
 (0%nat < q)%R ->
 (q < powerRZ radix e)%R -> r = p :>R \/ r = (p + powerRZ radix e)%R :>R.
intros P p q r e Rp H' H'0 H'1 H'2 H'3 H'4 H'5 H'6.
cut (p < p + q)%R; [ intros Rlt1 | idtac ].
cut (p + q < FNSucc b radix precision p)%R; [ intros Rlt2 | idtac ].
cut (isMin b radix (p + q) p); [ intros Min1 | idtac ].
cut (isMax b radix (p + q) (FNSucc b radix precision p));
 [ intros Max1 | idtac ].
cut (MinOrMaxP b radix P);
 [ intros MinOrMax | apply RoundedModeP_inv3 with (1 := Rp); auto ].
case (MinOrMax (p + q)%R r); auto; intros H1.
left.
apply (MinUniqueP b radix (p + q)%R); auto.
right.
cut ((p + powerRZ radix e)%R = FNSucc b radix precision p);
 [ intros Eq1; rewrite Eq1 | idtac ].
apply (MaxUniqueP b radix (p + q)%R); auto.
replace (FtoRradix (FNSucc b radix precision p)) with
 (Fnormalize radix b precision p +
  (FNSucc b radix precision p - Fnormalize radix b precision p))%R;
 [ idtac | ring ].
unfold FNSucc in |- *; rewrite <- (Fminus_correct radix); auto with arith;
 rewrite (FSuccDiff1 b radix precision); auto with arith.
rewrite (boundedNorMinGivesExp radix) with (x := e); auto with zarith.
rewrite (FnormalizeCorrect radix); auto; unfold FtoRradix, FtoR in |- *;
 simpl in |- *; ring.
apply sym_not_equal; apply Zlt_not_eq.
apply Zle_lt_trans with 0%Z; auto with zarith.
replace 0%Z with (- (0))%Z; auto with zarith; apply Zle_Zopp;
 apply Zlt_le_weak; apply nNormPos; auto with zarith.
apply (LtR0Fnum radix); auto.
rewrite FnormalizeCorrect; fold FtoRradix in |- *; auto.
apply Rlt_le_trans with (2 := H'3).
apply (LtFnumZERO radix); simpl in |- *;
 (replace 0%Z with (Z_of_nat 0); auto with zarith arith).
apply MinMax; auto with arith.
Contradict Rlt1.
rewrite Rlt1; auto with real.
apply MinBinade with (precision := precision); auto with arith.
apply Rlt_le; auto.
replace (FtoRradix (FNSucc b radix precision p)) with
 (Fnormalize radix b precision p +
  (FNSucc b radix precision p - Fnormalize radix b precision p))%R;
 [ idtac | ring ].
unfold FNSucc in |- *; rewrite <- (Fminus_correct radix); auto with arith;
 rewrite (FSuccDiff1 b radix precision); auto with arith.
rewrite (boundedNorMinGivesExp radix) with (x := e); auto with zarith.
rewrite (FnormalizeCorrect radix); auto; fold FtoRradix in |- *.
replace (FtoRradix (Float 1%nat e)) with (powerRZ radix e); auto with real.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
apply sym_not_equal; apply Zlt_not_eq.
apply Zle_lt_trans with 0%Z; auto with zarith.
replace 0%Z with (- (0))%Z; auto with zarith; apply Zle_Zopp;
 apply Zlt_le_weak; apply nNormPos; auto with zarith.
apply (LtR0Fnum radix); auto.
rewrite FnormalizeCorrect; fold FtoRradix in |- *; auto.
apply Rlt_le_trans with (2 := H'3).
apply (LtFnumZERO radix); simpl in |- *;
 (replace 0%Z with (Z_of_nat 0); auto with zarith arith).
pattern (FtoRradix p) at 1 in |- *; replace (FtoRradix p) with (p + 0)%R;
 [ idtac | ring ].
apply Rplus_lt_compat_l; auto.
Qed.
 
End FRoundP.
Hint Resolve FulpSucCan FulpSuc FulpPredCan FulpPred: float.