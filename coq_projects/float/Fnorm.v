(****************************************************************************
                                                                             
          IEEE754  :  Fnorm                                                     
                                                                             
          Laurent Thery  &  Sylvie Boldo                                                    
                                                                             
  ******************************************************************************)
Require Export Fbound.
 
Section Fnormalized_Def.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
 
Let FtoRradix := FtoR radix.
Coercion FtoRradix : float >-> R.
Variable b : Fbound.
 
Definition Fnormal (p : float) :=
  Fbounded b p /\ (Zpos (vNum b) <= Zabs (radix * Fnum p))%Z.
 
Theorem FnormalBounded : forall p : float, Fnormal p -> Fbounded b p.
intros p H; case H; auto.
Qed.
 
Theorem FnormalBound :
 forall p : float,
 Fnormal p -> (Zpos (vNum b) <= Zabs (radix * Fnum p))%Z.
intros p H; case H; auto.
Qed.
Hint Resolve FnormalBounded FnormalBound: float.
 
Theorem FnormalNotZero : forall p : float, Fnormal p -> ~ is_Fzero p.
unfold is_Fzero in |- *; intros p H; red in |- *; intros H1.
case H; rewrite H1.
replace (Zabs (radix * 0)) with 0%Z; auto with zarith.
rewrite Zmult_comm; simpl in |- *; auto.
Qed.
 
Theorem FnormalFop : forall p : float, Fnormal p -> Fnormal (Fopp p).
intros p H; split; auto with float.
replace (Zabs (radix * Fnum (Fopp p))) with (Zabs (radix * Fnum p));
 auto with float.
case p; simpl in |- *; auto with zarith.
intros Fnum1 Fexp1; rewrite <- Zopp_mult_distr_r; apply sym_equal;
 apply Zabs_Zopp.
Qed.
 
Theorem FnormalFabs : forall p : float, Fnormal p -> Fnormal (Fabs p).
intros p; case p; intros a e H; split; auto with float.
simpl in |- *; case H; intros H1 H2; simpl in |- *; auto.
rewrite <- (Zabs_eq radix); auto with zarith.
rewrite <- Zabs_Zmult.
rewrite (fun x => Zabs_eq (Zabs x)); auto with float zarith.
Qed.
 
Definition pPred x := Zpred (Zpos x).
 
Theorem maxMax1 :
 forall (p : float) (z : Z),
 Fbounded b p -> (Fexp p <= z)%Z -> (Fabs p <= Float (pPred (vNum b)) z)%R.
intros p z H H0; unfold FtoRradix in |- *.
rewrite <-
 (FshiftCorrect _ radixMoreThanOne (Zabs_nat (z - Fexp p))
    (Float (pPred (vNum b)) z)).
unfold FtoR, Fabs in |- *; simpl in |- *; auto with zarith.
rewrite Rmult_IZR; rewrite Zpower_nat_Z_powerRZ; auto with zarith.
repeat rewrite inj_abs; auto with zarith.
replace (z - (z - Fexp p))%Z with (Fexp p); [ idtac | ring ].
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
replace (z - Fexp p + Fexp p)%Z with z; [ idtac | ring ].
apply Rle_trans with (pPred (vNum b) * powerRZ radix (Fexp p))%R.
apply Rle_monotone_exp; auto with zarith; repeat rewrite Rmult_IZR;
 apply Rle_IZR; unfold pPred in |- *; apply Zle_Zpred;
 auto with float real zarith.
apply Rmult_le_compat_l; auto with real zarith.
replace 0%R with (IZR 0); auto with real; apply Rle_IZR; unfold pPred in |- *;
 apply Zle_Zpred; auto with float zarith.
apply Rle_powerRZ; auto with float real zarith.
Qed.
 
Theorem FnormalBoundAbs :
 forall p : float,
 Fnormal p -> (Float (pPred (vNum b)) (Zpred (Fexp p)) < Fabs p)%R.
intros p H'; unfold FtoRradix, FtoR in |- *; simpl in |- *.
pattern (Fexp p) at 2 in |- *; replace (Fexp p) with (Zsucc (Zpred (Fexp p)));
 [ rewrite powerRZ_Zs; auto with real zarith
 | unfold Zsucc, Zpred in |- *; ring ].
repeat rewrite <- Rmult_assoc.
apply Rmult_lt_compat_r; auto with real arith.
rewrite <- Rmult_IZR; apply Rlt_IZR.
unfold pPred in |- *; cut (Zpos (vNum b) <= Zabs (Fnum p) * radix)%Z;
 auto with zarith.
rewrite <- (Zabs_eq radix); auto with float zarith; rewrite <- Zabs_Zmult;
 rewrite Zmult_comm; auto with float real zarith.
Qed.
 
Definition Fsubnormal (p : float) :=
  Fbounded b p /\
  Fexp p = (- dExp b)%Z /\ (Zabs (radix * Fnum p) < Zpos (vNum b))%Z.
 
Theorem FsubnormalFbounded : forall p : float, Fsubnormal p -> Fbounded b p.
intros p H; case H; auto.
Qed.
 
Theorem FsubnormalFexp :
 forall p : float, Fsubnormal p -> Fexp p = (- dExp b)%Z.
intros p H; case H; auto.
intros H1 H2; case H2; auto.
Qed.
 
Theorem FsubnormalBound :
 forall p : float,
 Fsubnormal p -> (Zabs (radix * Fnum p) < Zpos (vNum b))%Z.
intros p H; case H; auto.
intros H1 H2; case H2; auto.
Qed.
Hint Resolve FsubnormalFbounded FsubnormalBound FsubnormalFexp: float.
 
Theorem FsubnormFopp : forall p : float, Fsubnormal p -> Fsubnormal (Fopp p).
intros p H'; repeat split; simpl in |- *; auto with zarith float.
rewrite Zabs_Zopp; auto with float.
rewrite <- Zopp_mult_distr_r; rewrite Zabs_Zopp; auto with float.
Qed.
 
Theorem FsubnormFabs : forall p : float, Fsubnormal p -> Fsubnormal (Fabs p).
intros p; case p; intros a e H; split; auto with float.
simpl in |- *; split; auto with float.
case H; intros H1 (H2, H3); auto.
rewrite <- (Zabs_eq radix); auto with zarith.
rewrite <- Zabs_Zmult.
rewrite (fun x => Zabs_eq (Zabs x)); auto with float zarith.
case H; intros H1 (H2, H3); auto.
Qed.
 
Theorem FsubnormalUnique :
 forall p q : float, Fsubnormal p -> Fsubnormal q -> p = q :>R -> p = q.
intros p q H' H'0 H'1.
apply FtoREqInv2 with (radix := radix); auto.
generalize H' H'0; unfold Fsubnormal in |- *; auto with zarith.
Qed.
 
Theorem FsubnormalLt :
 forall p q : float,
 Fsubnormal p -> Fsubnormal q -> (p < q)%R -> (Fnum p < Fnum q)%Z.
intros p q H' H'0 H'1.
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with zarith.
apply trans_equal with (- dExp b)%Z.
case H'; auto.
intros H1 H2; case H2; auto.
apply sym_equal; case H'0; auto.
intros H1 H2; case H2; auto.
Qed.
 
Theorem LtFsubnormal :
 forall p q : float,
 Fsubnormal p -> Fsubnormal q -> (Fnum p < Fnum q)%Z -> (p < q)%R.
intros p q H' H'0 H'1.
case (Rtotal_order p q); auto; intros Test; case Test; clear Test;
 intros Test; Contradict H'1.
unfold FtoRradix in Test; rewrite sameExpEq with (2 := Test); auto.
auto with zarith.
apply trans_equal with (- dExp b)%Z.
case H'; auto.
intros H1 H2; case H2; auto.
apply sym_equal; case H'0.
intros H1 H2; case H2; auto.
apply Zle_not_lt.
apply Zlt_le_weak.
apply FsubnormalLt; auto.
Qed.
 
Definition Fcanonic (a : float) := Fnormal a \/ Fsubnormal a.
 
Theorem FcanonicBound : forall p : float, Fcanonic p -> Fbounded b p.
intros p H; case H; auto with float.
Qed.
Hint Resolve FcanonicBound: float.
 
Theorem pUCanonic_absolu :
 forall p : float, Fcanonic p -> (Zabs (Fnum p) < Zpos (vNum b))%Z.
auto with float.
Qed.
 
Theorem FcanonicFopp : forall p : float, Fcanonic p -> Fcanonic (Fopp p).
intros p H'; case H'; intros H'1.
left; apply FnormalFop; auto.
right; apply FsubnormFopp; auto.
Qed.
 
Theorem FcanonicFabs : forall p : float, Fcanonic p -> Fcanonic (Fabs p).
intros p H'; case H'; clear H'; auto with float.
intros H; left; auto with float.
apply FnormalFabs; auto.
intros H; right; auto with float.
apply FsubnormFabs; auto.
Qed.
 
Theorem NormalNotSubNormal : forall p : float, ~ (Fnormal p /\ Fsubnormal p).
intros p; red in |- *; intros H; elim H; intros H0 H1; clear H.
absurd (Zabs (radix * Fnum p) < Zpos (vNum b))%Z;
 auto with float zarith.
Qed.
 
Theorem MaxFloat :
 forall x : float,
 Fbounded b x -> (Rabs x < Float (Zpos (vNum b)) (Fexp x))%R.
intros.
replace (Rabs x) with (FtoR radix (Fabs x)).
unfold FtoRradix in |- *.
apply maxMax with (b := b); auto with *.
unfold FtoRradix in |- *.
apply Fabs_correct; auto with *.
Qed.
(* What depends of the precision *)
Variable precision : nat.
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem FboundNext :
 forall p : float,
 Fbounded b p ->
 exists q : float, Fbounded b q /\ q = Float (Zsucc (Fnum p)) (Fexp p) :>R.
intros p H'.
case (Zle_lt_or_eq (Zsucc (Fnum p)) (Zpos (vNum b))); auto with float.
case (Zle_or_lt 0 (Fnum p)); intros H1.
rewrite <- (Zabs_eq (Fnum p)); auto with float zarith.
apply Zle_trans with 0%Z; auto with zarith.
intros H'0; exists (Float (Zsucc (Fnum p)) (Fexp p)); split; auto with float.
repeat split; simpl in |- *; auto with float.
case (Zle_or_lt 0 (Fnum p)); intros H1; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply Zlt_trans with (Zabs (Fnum p)); auto with float zarith.
repeat rewrite Zabs_eq_opp; auto with zarith.
intros H'0;
 exists (Float (Zpower_nat radix (pred precision)) (Zsucc (Fexp p))); 
 split; auto.
repeat split; simpl in |- *; auto with zarith arith float.
rewrite pGivesBound.
rewrite Zabs_eq; auto with zarith.
rewrite H'0; rewrite pGivesBound.
pattern precision at 2 in |- *; replace precision with (1 + pred precision).
rewrite Zpower_nat_is_exp.
rewrite Zpower_nat_1.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith.
rewrite Rmult_IZR; ring.
generalize precisionNotZero; case precision; simpl in |- *; auto with arith.
intros H'1; case H'1; auto.
Qed.
 
Theorem digitPredVNumiSPrecision :
 digit radix (Zpred (Zpos (vNum b))) = precision.
apply digitInv; auto.
rewrite pGivesBound.
rewrite Zabs_eq; auto with zarith.
rewrite Zabs_eq; auto with zarith.
Qed.
 
Theorem digitVNumiSPrecision :
 digit radix (Zpos (vNum b)) = S precision.
apply digitInv; auto.
rewrite pGivesBound.
rewrite Zabs_eq; auto with zarith.
rewrite Zabs_eq; auto with zarith.
rewrite pGivesBound; auto with zarith.
Qed.
 
Theorem vNumPrecision :
 forall n : Z,
 digit radix n <= precision -> (Zabs n < Zpos (vNum b))%Z.
intros n H'.
rewrite <- (Zabs_eq (Zpos (vNum b))); auto with zarith.
apply digit_anti_monotone_lt with (n := radix); auto.
rewrite digitVNumiSPrecision; auto with arith.
Qed.
 
Theorem pGivesDigit :
 forall p : float, Fbounded b p -> Fdigit radix p <= precision.
intros p H; unfold Fdigit in |- *.
rewrite <- digitPredVNumiSPrecision.
apply digit_monotone; auto with zarith.
rewrite (fun x => Zabs_eq (Zpred x)); auto with float zarith.
Qed.
 
Theorem digitGivesBoundedNum :
 forall p : float,
 Fdigit radix p <= precision -> (Zabs (Fnum p) < Zpos (vNum b))%Z.
intros p H; apply vNumPrecision; auto.
Qed.
 
Theorem FboundedOne :
 forall z : Z, (- dExp b <= z)%Z -> Fbounded b (Float 1%nat z).
intros z H'; repeat (split; simpl in |- *; auto with zarith).
rewrite pGivesBound; auto.
apply Zlt_le_trans with (Zpower_nat radix 1); auto with zarith.
rewrite Zpower_nat_1; auto with zarith.
Qed.
 
Theorem FboundedMboundPos :
 forall z m : Z,
 (0 <= m)%Z ->
 (m <= Zpower_nat radix precision)%Z ->
 (- dExp b <= z)%Z ->
 exists c : float, Fbounded b c /\ c = (m * powerRZ radix z)%R :>R.
intros z m H' H'0 H'1; case (Zle_lt_or_eq _ _ H'0); intros H'2.
exists (Float m z); split; auto with zarith.
repeat split; simpl in |- *; auto with zarith.
rewrite Zabs_eq; auto; rewrite pGivesBound; auto.
case (FboundNext (Float (Zpred (Zpos (vNum b))) z)); auto with float.
intros f' (H1, H2); exists f'; split; auto.
rewrite H2; rewrite pGivesBound.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
rewrite <- Zsucc_pred; rewrite <- H'2; auto; ring.
Qed.
 
Theorem FboundedMbound :
 forall z m : Z,
 (Zabs m <= Zpower_nat radix precision)%Z ->
 (- dExp b <= z)%Z ->
 exists c : float, Fbounded b c /\ c = (m * powerRZ radix z)%R :>R.
intros z m H H0.
case (Zle_or_lt 0 m); intros H1.
case (FboundedMboundPos z (Zabs m)); auto; try rewrite Zabs_eq; auto.
intros f (H2, H3); exists f; split; auto.
case (FboundedMboundPos z (Zabs m)); auto; try rewrite Zabs_eq_opp;
 auto with zarith.
intros f (H2, H3); exists (Fopp f); split; auto with float.
rewrite (Fopp_correct radix); auto with arith; fold FtoRradix in |- *;
 rewrite H3.
rewrite Ropp_Ropp_IZR; ring.
Qed.
 
Theorem FnormalPrecision :
 forall p : float, Fnormal p -> Fdigit radix p = precision.
intros p H; apply le_antisym; auto with float.
apply pGivesDigit; auto with float.
apply le_S_n.
rewrite <- digitVNumiSPrecision.
unfold Fdigit in |- *.
replace (S (digit radix (Fnum p))) with (digit radix (Fnum p) + 1).
rewrite <- digitAdd; auto with zarith.
apply digit_monotone; auto with float.
rewrite (fun x => Zabs_eq (Zpos x)); auto with float zarith.
rewrite Zmult_comm; rewrite Zpower_nat_1; auto with float zarith.
red in |- *; intros H1; case H.
intros H0 H2; Contradict H2; rewrite H1.
replace (Zabs (radix * 0)) with 0%Z; auto with zarith.
rewrite Zmult_comm; simpl in |- *; auto.
rewrite plus_comm; simpl in |- *; auto.
Qed.
Hint Resolve FnormalPrecision: float.
 
Theorem FnormalUnique :
 forall p q : float, Fnormal p -> Fnormal q -> p = q :>R -> p = q.
intros p q H' H'0 H'1.
apply (FdigitEq radix); auto.
apply FnormalNotZero; auto.
apply trans_equal with (y := precision); auto with float.
apply sym_equal; auto with float.
Qed.
 
Theorem FnormalLtPos :
 forall p q : float,
 Fnormal p ->
 Fnormal q ->
 (0 <= p)%R ->
 (p < q)%R -> (Fexp p < Fexp q)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
intros p q H' H'0 H'1 H'2.
case (Zle_or_lt (Fexp q) (Fexp p)); auto.
intros H'3; right.
case (Zle_lt_or_eq _ _ H'3); intros H'4.
2: split; auto.
2: apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with zarith.
absurd (Fnum (Fshift radix (Zabs_nat (Fexp p - Fexp q)) p) < Fnum q)%Z; auto.
2: apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with zarith.
2: unfold FtoRradix in |- *; rewrite FshiftCorrect; auto.
2: unfold Fshift in |- *; simpl in |- *; auto with zarith.
2: replace (Z_of_nat (Zabs_nat (Fexp p - Fexp q))) with (Fexp p - Fexp q)%Z;
    auto with zarith.
2: cut (0 < Fexp p - Fexp q)%Z; auto with zarith.
2: case (Fexp p - Fexp q)%Z; simpl in |- *; auto with zarith.
2: intros p0; rewrite (inject_nat_convert (Zpos p0)); auto with arith.
2: intros p0 H'5; discriminate.
red in |- *; intros H'5.
absurd
 (Fdigit radix (Fshift radix (Zabs_nat (Fexp p - Fexp q)) p) <=
  Fdigit radix q); auto with arith.
rewrite FshiftFdigit; auto with arith.
replace (Fdigit radix p) with precision.
replace (Fdigit radix q) with precision; auto with zarith.
cut (0 < Fexp p - Fexp q)%Z; auto with zarith.
case (Fexp p - Fexp q)%Z; simpl in |- *; auto with zarith.
intros p0 H'6; generalize (convert_not_O p0); auto with zarith.
intros p0 H'6; discriminate.
apply sym_equal; auto with float.
apply sym_equal; auto with float.
apply FnormalNotZero; auto with arith.
unfold Fdigit in |- *; apply digit_monotone; auto with arith.
repeat rewrite Zabs_eq; auto with zarith.
apply LeR0Fnum with (radix := radix); auto with zarith.
apply Rle_trans with (r2 := FtoRradix p); auto with real.
apply LeR0Fnum with (radix := radix); auto with zarith.
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto.
Qed.
 
Theorem FnormalLtNeg :
 forall p q : float,
 Fnormal p ->
 Fnormal q ->
 (q <= 0)%R ->
 (p < q)%R -> (Fexp q < Fexp p)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
intros p q H' H'0 H'1 H'2.
cut
 ((Fexp (Fopp q) < Fexp (Fopp p))%Z \/
  Fexp (Fopp q) = Fexp (Fopp p) /\ (Fnum (Fopp q) < Fnum (Fopp p))%Z).
simpl in |- *.
intros H'3; elim H'3; clear H'3; intros H'3;
 [ idtac | elim H'3; clear H'3; intros H'3 H'4 ]; auto; 
 right; split; auto with zarith.
apply FnormalLtPos; try apply FnormalFop; auto; unfold FtoRradix in |- *;
 repeat rewrite Fopp_correct; replace 0%R with (-0)%R; 
 auto with real.
Qed.
 
Definition nNormMin := Zpower_nat radix (pred precision).
 
Theorem nNormPos : (0 < nNormMin)%Z.
unfold nNormMin in |- *; auto with zarith.
Qed.
 
Theorem digitnNormMin : digit radix nNormMin = precision.
unfold nNormMin, Fdigit in |- *; simpl in |- *; apply digitInv;
 auto with zarith arith.
rewrite Zabs_eq; auto with zarith.
Qed.
 
Theorem nNrMMimLevNum : (nNormMin <= Zpos (vNum b))%Z.
rewrite pGivesBound.
unfold nNormMin in |- *; simpl in |- *; auto with zarith arith.
Qed.
Hint Resolve nNrMMimLevNum: arith.
 
Definition firstNormalPos := Float nNormMin (- dExp b).
 
Theorem firstNormalPosNormal : Fnormal firstNormalPos.
repeat split; unfold firstNormalPos in |- *; simpl in |- *; auto with zarith.
rewrite pGivesBound.
rewrite Zabs_eq; auto with zarith.
unfold nNormMin in |- *; simpl in |- *; auto with zarith arith.
apply Zlt_le_weak; auto with zarith.
apply nNormPos.
rewrite pGivesBound.
replace precision with (pred precision + 1).
rewrite Zpower_nat_is_exp; auto with zarith.
rewrite Zpower_nat_1; auto with zarith.
rewrite (fun x => Zmult_comm x radix); unfold nNormMin in |- *;
 auto with zarith.
unfold nNormMin in |- *; auto with zarith.
Qed.
 
Theorem pNormal_absolu_min :
 forall p : float, Fnormal p -> (nNormMin <= Zabs (Fnum p))%Z.
intros p H; apply Zmult_le_reg_r with (p := radix); auto with zarith.
unfold nNormMin in |- *.
pattern radix at 2 in |- *; rewrite <- (Zpower_nat_1 radix).
rewrite <- Zpower_nat_is_exp; auto with zarith.
replace (pred precision + 1) with precision.
rewrite <- pGivesBound; auto with float.
rewrite <- (Zabs_eq radix); auto with zarith.
rewrite <- Zabs_Zmult; rewrite Zmult_comm; auto with float.
generalize precisionNotZero; case precision; simpl in |- *;
 try (intros tmp; Contradict tmp; auto; fail); intros; 
 rewrite plus_comm; simpl in |- *; auto.
Qed.
 
Theorem maxMaxBis :
 forall (p : float) (z : Z),
 Fbounded b p -> (Fexp p < z)%Z -> (Fabs p < Float nNormMin z)%R.
intros p z H' H'0;
 apply
  Rlt_le_trans with (FtoR radix (Float (Zpos (vNum b)) (Zpred z))).
unfold FtoRradix in |- *; apply maxMax; auto with zarith;
 unfold Zpred in |- *; auto with zarith.
unfold FtoRradix, FtoR, nNormMin in |- *; simpl in |- *.
pattern z at 2 in |- *; replace z with (Zsucc (Zpred z));
 [ rewrite powerRZ_Zs; auto with real zarith
 | unfold Zsucc, Zpred in |- *; ring ].
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; auto with real arith.
pattern radix at 2 in |- *; rewrite <- (Zpower_nat_1 radix).
rewrite <- Rmult_IZR.
rewrite <- Zpower_nat_is_exp.
replace (pred precision + 1) with precision.
replace (INR (nat_of_P (vNum b))) with (IZR (Zpos (vNum b))).
rewrite pGivesBound; auto with real.
simpl; unfold IZR; rewrite <- INR_IPR; auto.
generalize precisionNotZero; case precision; simpl in |- *; auto with arith.
intros H'1; Contradict H'1; auto.
intros; rewrite plus_comm; simpl in |- *; auto.
Qed.
 
Theorem FnormalLtFirstNormalPos :
 forall p : float, Fnormal p -> (0 <= p)%R -> (firstNormalPos <= p)%R.
intros p H' H'0.
case (Rle_or_lt firstNormalPos p); intros Lt0; auto with real.
case (FnormalLtPos p firstNormalPos); auto.
apply firstNormalPosNormal.
intros H'1; Contradict H'1; unfold firstNormalPos in |- *; simpl in |- *.
apply Zle_not_lt; auto with float.
intros H'1; elim H'1; intros H'2 H'3; Contradict H'3.
unfold firstNormalPos in |- *; simpl in |- *.
apply Zle_not_lt.
rewrite <- (Zabs_eq (Fnum p)); auto with float zarith.
apply pNormal_absolu_min; auto.
apply LeR0Fnum with (radix := radix); auto with arith.
Qed.
 
Theorem FnormalLtFirstNormalNeg :
 forall p : float, Fnormal p -> (p <= 0)%R -> (p <= Fopp firstNormalPos)%R.
intros p H' H'0.
rewrite <- (Ropp_involutive p); unfold FtoRradix in |- *;
 repeat rewrite Fopp_correct.
apply Ropp_le_contravar; rewrite <- Fopp_correct.
apply FnormalLtFirstNormalPos.
apply FnormalFop; auto.
replace 0%R with (-0)%R; unfold FtoRradix in |- *; try rewrite Fopp_correct;
 auto with real.
Qed.
 
Theorem FsubnormalDigit :
 forall p : float, Fsubnormal p -> Fdigit radix p < precision.
intros p H; unfold Fdigit in |- *.
case (Z_eq_dec (Fnum p) 0); intros Z1.
rewrite Z1; simpl in |- *; auto with arith.
apply lt_S_n; apply le_lt_n_Sm.
rewrite <- digitPredVNumiSPrecision.
replace (S (digit radix (Fnum p))) with (digit radix (Fnum p) + 1).
rewrite <- digitAdd; auto with zarith.
apply digit_monotone; auto with float.
rewrite (fun x => Zabs_eq (Zpred x)); auto with float zarith.
rewrite Zmult_comm; rewrite Zpower_nat_1; auto with float zarith.
rewrite plus_comm; simpl in |- *; auto.
Qed.
Hint Resolve FsubnormalDigit: float.
 
Theorem pSubnormal_absolu_min :
 forall p : float, Fsubnormal p -> (Zabs (Fnum p) < nNormMin)%Z.
intros p H'; apply Zlt_mult_simpl_l with (c := radix); auto with zarith.
replace (radix * Zabs (Fnum p))%Z with (Zabs (radix * Fnum p)).
replace (radix * nNormMin)%Z with (Zpos (vNum b)); auto with float.
rewrite pGivesBound.
replace precision with (1 + pred precision).
rewrite Zpower_nat_is_exp; auto with zarith; rewrite Zpower_nat_1; auto.
generalize precisionNotZero; case precision; simpl in |- *; auto.
intros H; Contradict H; auto.
rewrite Zabs_Zmult; rewrite (Zabs_eq radix); auto with zarith.
Qed.
 
Theorem FsubnormalLtFirstNormalPos :
 forall p : float, Fsubnormal p -> (0 <= p)%R -> (p < firstNormalPos)%R.
intros p H' H'0; unfold FtoRradix, FtoR, firstNormalPos in |- *;
 simpl in |- *.
replace (Fexp p) with (- dExp b)%Z.
2: apply sym_equal; case H'; intros H1 H2; case H2; auto.
apply Rmult_lt_compat_r; auto with real arith.
apply Rlt_IZR.
rewrite <- (Zabs_eq (Fnum p)).
2: apply LeR0Fnum with (radix := radix); auto with zarith.
apply pSubnormal_absolu_min; auto.
Qed.
 
Theorem FsubnormalnormalLtPos :
 forall p q : float,
 Fsubnormal p -> Fnormal q -> (0 <= p)%R -> (0 <= q)%R -> (p < q)%R.
intros p q H' H'0 H'1 H'2.
apply Rlt_le_trans with (r2 := FtoRradix firstNormalPos).
apply FsubnormalLtFirstNormalPos; auto.
apply FnormalLtFirstNormalPos; auto.
Qed.
 
Theorem FsubnormalnormalLtNeg :
 forall p q : float,
 Fsubnormal p -> Fnormal q -> (p <= 0)%R -> (q <= 0)%R -> (q < p)%R.
intros p q H' H'0 H'1 H'2.
rewrite <- (Ropp_involutive p); rewrite <- (Ropp_involutive q).
apply Ropp_gt_lt_contravar; red in |- *.
unfold FtoRradix in |- *; repeat rewrite <- Fopp_correct.
apply FsubnormalnormalLtPos; auto.
apply FsubnormFopp; auto.
apply FnormalFop; auto.
unfold FtoRradix in |- *; rewrite Fopp_correct; replace 0%R with (-0)%R;
 auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct; replace 0%R with (-0)%R;
 auto with real.
Qed.
 
Definition Fnormalize (p : float) :=
  match Z_zerop (Fnum p) with
  | left _ => Float 0 (- dExp b)
  | right _ =>
      Fshift radix
        (min (precision - Fdigit radix p) (Zabs_nat (dExp b + Fexp p))) p
  end.
 
Theorem FnormalizeCorrect : forall p : float, Fnormalize p = p :>R.
intros p; unfold Fnormalize in |- *.
case (Z_zerop (Fnum p)).
case p; intros Fnum1 Fexp1 H'; unfold FtoRradix, FtoR in |- *; rewrite H';
 simpl in |- *; auto with real.
apply trans_eq with 0%R; auto with real.
intros H'; unfold FtoRradix in |- *; apply FshiftCorrect; auto.
Qed.
 
Theorem Fnormalize_Fopp :
 forall p : float, Fnormalize (Fopp p) = Fopp (Fnormalize p).
intros p; case p; unfold Fnormalize in |- *; simpl in |- *.
intros Fnum1 Fexp1; case (Z_zerop Fnum1); intros H'.
rewrite H'; simpl in |- *; auto.
case (Z_zerop (- Fnum1)); intros H'0; simpl in |- *; auto.
case H'; replace Fnum1 with (- - Fnum1)%Z; auto with zarith.
unfold Fopp, Fshift, Fdigit in |- *; simpl in |- *.
replace (digit radix (- Fnum1)) with (digit radix Fnum1).
apply floatEq; simpl in |- *; auto with zarith.
ring.
case Fnum1; simpl in |- *; auto.
Qed.
 
Theorem FnormalizeBounded :
 forall p : float, Fbounded b p -> Fbounded b (Fnormalize p).
intros p H'; red in |- *; split.
unfold Fnormalize in |- *; case (Z_zerop (Fnum p)); auto.
intros H'0; simpl in |- *; auto with zarith.
intros H'0.
apply digitGivesBoundedNum; auto.
rewrite FshiftFdigit; auto.
apply le_trans with (m := Fdigit radix p + (precision - Fdigit radix p));
 auto with arith.
rewrite <- le_plus_minus; auto.
apply pGivesDigit; auto.
unfold Fnormalize in |- *; case (Z_zerop (Fnum p)); auto.
simpl in |- *; auto with zarith.
generalize H'; case p; unfold Fbounded, Fnormal, Fdigit in |- *;
 simpl in |- *.
intros Fnum1 Fexp1 H'0 H'1.
apply Zle_trans with (m := (Fexp1 - Zabs_nat (dExp b + Fexp1))%Z).
rewrite inj_abs; auto with zarith.
unfold Zminus in |- *; apply Zplus_le_compat_l; auto.
apply Zle_Zopp; auto.
apply inj_le; auto with arith.
Qed.
 
Theorem FnormalizeCanonic :
 forall p : float, Fbounded b p -> Fcanonic (Fnormalize p).
intros p H'.
generalize (FnormalizeBounded p H').
unfold Fnormalize in |- *; case (Z_zerop (Fnum p)); auto.
intros H'0; right; repeat split; simpl in |- *; auto with zarith.
rewrite Zmult_comm; simpl in |- *; red in |- *; simpl in |- *; auto.
intros H'1.
case (min_or (precision - Fdigit radix p) (Zabs_nat (dExp b + Fexp p)));
 intros Min; case Min; clear Min; intros MinR MinL.
intros H'2; left; split; auto.
rewrite MinR; unfold Fshift in |- *; simpl in |- *.
apply
 Zle_trans
  with
    (Zabs
       (radix *
        (Zpower_nat radix (pred (Fdigit radix p)) *
         Zpower_nat radix (precision - Fdigit radix p)))).
pattern radix at 1 in |- *; rewrite <- (Zpower_nat_1 radix).
repeat rewrite <- Zpower_nat_is_exp; auto with zarith.
replace (1 + (pred (Fdigit radix p) + (precision - Fdigit radix p))) with
 precision; auto.
rewrite pGivesBound; auto with real.
rewrite Zabs_eq; auto with zarith.
cut (Fdigit radix p <= precision); auto with float.
unfold Fdigit in |- *.
generalize (digitNotZero _ radixMoreThanOne _ H'1);
 case (digit radix (Fnum p)); simpl in |- *; auto.
intros tmp; Contradict tmp; auto with arith.
intros n H H0; change (precision = S n + (precision - S n)) in |- *.
apply le_plus_minus; auto.
apply pGivesDigit; auto.
repeat rewrite Zabs_Zmult.
apply Zle_Zmult_comp_l.
apply Zle_ZERO_Zabs.
apply Zle_Zmult_comp_r.
apply Zle_ZERO_Zabs.
rewrite (fun x => Zabs_eq (Zpower_nat radix x)); auto with zarith.
unfold Fdigit in |- *; apply digitLess; auto.
intros H'0; right; split; auto; split.
rewrite MinR; clear MinR; auto.
cut (- dExp b <= Fexp p)%Z; [ idtac | auto with float ].
case p; simpl in |- *.
intros Fnum1 Fexp1 H'2; rewrite inj_abs; auto with zarith.
rewrite MinR.
rewrite <- (fun x => Zabs_eq (Zpos x)).
unfold Fshift in |- *; simpl in |- *.
apply
 Zlt_le_trans
  with
    (Zabs
       (radix *
        (Zpower_nat radix (Fdigit radix p) *
         Zpower_nat radix (Zabs_nat (dExp b + Fexp p))))).
repeat rewrite Zabs_Zmult.
apply Zmult_gt_0_lt_compat_l.
apply Zlt_gt; rewrite Zabs_eq; auto with zarith.
apply Zmult_gt_0_lt_compat_r.
apply Zlt_gt; rewrite Zabs_eq; auto with zarith.
rewrite (fun x => Zabs_eq (Zpower_nat radix x)); auto with zarith.
unfold Fdigit in |- *; apply digitMore; auto.
pattern radix at 1 in |- *; rewrite <- (Zpower_nat_1 radix).
repeat rewrite <- Zpower_nat_is_exp; auto with zarith.
apply Zle_trans with (Zabs (Zpower_nat radix precision)).
repeat rewrite Zabs_eq; auto with zarith.
rewrite pGivesBound.
rewrite (fun x => Zabs_eq (Zpower_nat radix x)); auto with zarith.
red in |- *; simpl in |- *; red in |- *; intros; discriminate.
Qed.
 
Theorem NormalAndSubNormalNotEq :
 forall p q : float, Fnormal p -> Fsubnormal q -> p <> q :>R.
intros p q H' H'0; red in |- *; intros H'1.
case (Rtotal_order 0 p); intros H'2.
absurd (q < p)%R.
rewrite <- H'1; auto with real.
apply FsubnormalnormalLtPos; auto with real.
rewrite <- H'1; auto with real.
absurd (p < q)%R.
rewrite <- H'1; auto with real.
apply FsubnormalnormalLtNeg; auto with real.
rewrite <- H'1; auto with real.
elim H'2; intros H'3; try rewrite <- H'3; auto with real.
elim H'2; intros H'3; try rewrite <- H'3; auto with real.
Qed.
 
Theorem FcanonicUnique :
 forall p q : float, Fcanonic p -> Fcanonic q -> p = q :>R -> p = q.
intros p q H' H'0 H'1; case H'; case H'0; intros H'2 H'3.
apply FnormalUnique; auto.
Contradict H'1; apply NormalAndSubNormalNotEq; auto.
absurd (q = p :>R); auto; apply NormalAndSubNormalNotEq; auto.
apply FsubnormalUnique; auto.
Qed.
 
Theorem FcanonicLeastExp :
 forall x y : float,
 x = y :>R -> Fbounded b x -> Fcanonic y -> (Fexp y <= Fexp x)%Z.
intros x y H H0 H1.
cut (Fcanonic (Fnormalize x)); [ intros | apply FnormalizeCanonic; auto ].
replace y with (Fnormalize x);
 [ simpl in |- * | apply FcanonicUnique; auto with real ].
unfold Fnormalize in |- *.
case (Z_zerop (Fnum x)); simpl in |- *; intros Z1; auto with float.
apply Zplus_le_reg_l with (- Fexp x)%Z.
replace (- Fexp x + Fexp x)%Z with (- (0))%Z; try ring.
replace
 (- Fexp x +
  (Fexp x - min (precision - Fdigit radix x) (Zabs_nat (dExp b + Fexp x))))%Z
 with (- min (precision - Fdigit radix x) (Zabs_nat (dExp b + Fexp x)))%Z;
 try ring.
apply Zle_Zopp; auto with arith zarith.
rewrite <- H.
apply FnormalizeCorrect.
Qed.
 
Theorem FcanonicLtPos :
 forall p q : float,
 Fcanonic p ->
 Fcanonic q ->
 (0 <= p)%R ->
 (p < q)%R -> (Fexp p < Fexp q)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
intros p q H' H'0 H'1 H'2; case H'; case H'0.
intros H'3 H'4; apply FnormalLtPos; auto.
intros H'3 H'4; absurd (p < q)%R; auto.
apply Rlt_asym.
apply FsubnormalnormalLtPos; auto.
apply Rle_trans with (r2 := FtoRradix p); auto with real.
intros H'3 H'4; case (Z_eq_dec (Fexp q) (- dExp b)); intros H'5.
right; split.
rewrite H'5; case H'4; intros H1 H2; case H2; auto.
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with zarith.
rewrite H'5; case H'4; intros H1 H2; case H2; auto.
left.
replace (Fexp p) with (- dExp b)%Z;
 [ idtac | apply sym_equal; auto with float ].
case (Zle_lt_or_eq (- dExp b) (Fexp q)); auto with float zarith.
intros H'3 H'4; right; split.
apply trans_equal with (- dExp b)%Z; auto with float.
apply sym_equal; auto with float.
apply FsubnormalLt; auto.
Qed.
 
Theorem FcanonicLePos :
 forall p q : float,
 Fcanonic p ->
 Fcanonic q ->
 (0 <= p)%R ->
 (p <= q)%R -> (Fexp p < Fexp q)%Z \/ Fexp p = Fexp q /\ (Fnum p <= Fnum q)%Z.
intros p q H' H'0 H'1 H'2.
case H'2; intros H'3.
case FcanonicLtPos with (p := p) (q := q); auto with zarith arith.
rewrite FcanonicUnique with (p := p) (q := q); auto with zarith arith.
Qed.
 
Theorem Fcanonic_Rle_Zle :
 forall x y : float,
 Fcanonic x -> Fcanonic y -> (Rabs x <= Rabs y)%R -> (Fexp x <= Fexp y)%Z.
intros x y H H0 H1.
cut (forall z : float, Fexp z = Fexp (Fabs z) :>Z);
 [ intros E | intros; unfold Fabs in |- *; simpl in |- *; auto with zarith ].
rewrite (E x); rewrite (E y).
cut (Fcanonic (Fabs x)); [ intros D | apply FcanonicFabs; auto ].
cut (Fcanonic (Fabs y)); [ intros G | apply FcanonicFabs; auto ].
case H1; intros Z2.
case (FcanonicLtPos (Fabs x) (Fabs y)); auto with zarith.
rewrite (Fabs_correct radix); auto with real zarith.
repeat rewrite (Fabs_correct radix); auto with real zarith.
rewrite (FcanonicUnique (Fabs x) (Fabs y)); auto with float zarith.
repeat rewrite (Fabs_correct radix); auto with real zarith.
Qed.
 
Theorem FcanonicLtNeg :
 forall p q : float,
 Fcanonic p ->
 Fcanonic q ->
 (q <= 0)%R ->
 (p < q)%R -> (Fexp q < Fexp p)%Z \/ Fexp p = Fexp q /\ (Fnum p < Fnum q)%Z.
intros p q H' H'0 H'1 H'2.
cut
 ((Fexp (Fopp q) < Fexp (Fopp p))%Z \/
  Fexp (Fopp q) = Fexp (Fopp p) /\ (Fnum (Fopp q) < Fnum (Fopp p))%Z).
simpl in |- *.
intros H'3; elim H'3; clear H'3; intros H'3;
 [ idtac | elim H'3; clear H'3; intros H'3 H'4 ]; auto; 
 right; split; auto with zarith.
apply FcanonicLtPos; try apply FcanonicFopp; auto; unfold FtoRradix in |- *;
 repeat rewrite Fopp_correct; replace 0%R with (-0)%R; 
 auto with real.
Qed.
 
Theorem FcanonicFnormalizeEq :
 forall p : float, Fcanonic p -> Fnormalize p = p.
intros p H'.
apply FcanonicUnique; auto.
apply FnormalizeCanonic; auto.
apply FcanonicBound with (1 := H'); auto.
apply FnormalizeCorrect; auto.
Qed.
 
Theorem FcanonicPosFexpRlt :
 forall x y : float,
 (0 <= x)%R ->
 (0 <= y)%R -> Fcanonic x -> Fcanonic y -> (Fexp x < Fexp y)%Z -> (x < y)%R.
intros x y H' H'0 H'1 H'2 H'3.
case (Rle_or_lt y x); auto.
intros H'4; case H'4; clear H'4; intros H'4.
case FcanonicLtPos with (p := y) (q := x); auto.
intros H'5; Contradict H'3; auto with zarith.
intros H'5; elim H'5; intros H'6 H'7; clear H'5; Contradict H'3; rewrite H'6;
 auto with zarith.
Contradict H'3.
rewrite FcanonicUnique with (p := x) (q := y); auto with zarith.
Qed.
 
Theorem FcanonicNegFexpRlt :
 forall x y : float,
 (x <= 0)%R ->
 (y <= 0)%R -> Fcanonic x -> Fcanonic y -> (Fexp x < Fexp y)%Z -> (y < x)%R.
intros x y H' H'0 H'1 H'2 H'3.
case (Rle_or_lt x y); auto.
intros H'4; case H'4; clear H'4; intros H'4.
case FcanonicLtNeg with (p := x) (q := y); auto.
intros H'5; Contradict H'3; auto with zarith.
intros H'5; elim H'5; intros H'6 H'7; clear H'5; Contradict H'3; rewrite H'6;
 auto with zarith.
Contradict H'3.
rewrite FcanonicUnique with (p := x) (q := y); auto with zarith.
Qed.
 
Theorem FnormalBoundAbs2 :
 forall p : float,
 Fnormal p ->
 (Zpos (vNum b) * Float 1%nat (Zpred (Fexp p)) <= Fabs p)%R.
intros p H'; unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (1 * powerRZ radix (Zpred (Fexp p)))%R with
 (powerRZ radix (Zpred (Fexp p))); [ idtac | ring ].
pattern (Fexp p) at 2 in |- *; replace (Fexp p) with (Zsucc (Zpred (Fexp p)));
 [ rewrite powerRZ_Zs; auto with real zarith
 | unfold Zsucc, Zpred in |- *; ring ].
repeat rewrite <- Rmult_assoc.
apply Rmult_le_compat_r; auto with real arith.
rewrite <- Rmult_IZR; apply Rle_IZR.
rewrite <- (Zabs_eq radix); auto with zarith.
rewrite <- Zabs_Zmult; rewrite Zmult_comm; auto with float.
Qed.
 
Theorem vNumbMoreThanOne : (1 < Zpos (vNum b))%Z.
replace 1%Z with (Z_of_nat 1); [ idtac | simpl in |- *; auto ].
rewrite <- (Zpower_nat_O radix); rewrite pGivesBound; auto with zarith.
Qed.
 
Theorem PosNormMin : Zpos (vNum b) = (radix * nNormMin)%Z.
pattern radix at 1 in |- *; rewrite <- (Zpower_nat_1 radix);
 unfold nNormMin in |- *.
rewrite pGivesBound; rewrite <- Zpower_nat_is_exp.
generalize precisionNotZero; case precision; auto with zarith.
Qed.
 
Theorem FnormalPpred :
 forall x : Z, (- dExp b <= x)%Z -> Fnormal (Float (pPred (vNum b)) x).
intros x H;
 (cut (0 <= pPred (vNum b))%Z;
   [ intros Z1 | unfold pPred in |- *; auto with zarith ]).
repeat split; simpl in |- *; auto with zarith.
rewrite (Zabs_eq (pPred (vNum b))).
unfold pPred in |- *; auto with zarith.
unfold pPred in |- *; rewrite pGivesBound; auto with zarith.
rewrite Zabs_Zmult; repeat rewrite Zabs_eq; auto with zarith.
apply Zle_trans with ((1 + 1) * pPred (vNum b))%Z; auto with zarith.
replace ((1 + 1) * pPred (vNum b))%Z with (pPred (vNum b) + pPred (vNum b))%Z;
 auto with zarith.
replace (Zpos (vNum b)) with (1 + Zpred (Zpos (vNum b)))%Z;
 unfold pPred in |- *; auto with zarith.
apply Zplus_le_compat_r; apply Zle_Zpred.
apply vNumbMoreThanOne.
Qed.
 
Theorem FcanonicPpred :
 forall x : Z,
 (- dExp b <= x)%Z -> Fcanonic (Float (pPred (vNum b)) x).
intros x H; left; apply FnormalPpred; auto.
Qed.
 
Theorem FnormalNnormMin :
 forall x : Z, (- dExp b <= x)%Z -> Fnormal (Float nNormMin x).
intros x H; (cut (0 < nNormMin)%Z; [ intros Z1 | apply nNormPos ]).
repeat split; simpl in |- *; auto with zarith.
rewrite Zabs_eq; auto with zarith.
rewrite PosNormMin.
pattern nNormMin at 1 in |- *; replace nNormMin with (1 * nNormMin)%Z;
 auto with zarith.
apply Zmult_gt_0_lt_compat_r; auto with zarith.
rewrite PosNormMin; auto with zarith.
Qed.
 
Theorem FcanonicNnormMin :
 forall x : Z, (- dExp b <= x)%Z -> Fcanonic (Float nNormMin x).
intros x H; left; apply FnormalNnormMin; auto.
Qed.
 
Theorem boundedNorMinGivesExp :
 forall (x : Z) (p : float),
 Fbounded b p ->
 (- dExp b <= x)%Z ->
 (Float nNormMin x <= p)%R ->
 (p <= Float (pPred (vNum b)) x)%R -> Fexp (Fnormalize p) = x.
intros x p H' H'0 H'1 H'2.
cut (0 <= p)%R; [ intros Rle1 | idtac ].
case (FcanonicLePos (Float nNormMin x) (Fnormalize p));
 try rewrite FnormalizeCorrect; simpl in |- *; auto with float zarith.
apply FcanonicNnormMin; auto.
apply FnormalizeCanonic; auto.
apply (LeFnumZERO radix); simpl in |- *; auto.
apply Zlt_le_weak; apply nNormPos.
intros H'3.
case (FcanonicLePos (Fnormalize p) (Float (pPred (vNum b)) x));
 try rewrite FnormalizeCorrect; simpl in |- *; auto.
apply FnormalizeCanonic; auto.
apply FcanonicPpred; auto.
intros H'4; Contradict H'4; auto with zarith.
intros (H'4, H'5); auto.
apply Rle_trans with (2 := H'1).
apply (LeFnumZERO radix); simpl in |- *; auto with zarith.
apply Zlt_le_weak; apply nNormPos.
Qed.
 
End Fnormalized_Def.
Hint Resolve FnormalBounded FnormalPrecision: float.
Hint Resolve FnormalNotZero nNrMMimLevNum firstNormalPosNormal FsubnormFopp
  FsubnormalLtFirstNormalPos FnormalizeBounded FcanonicFopp FcanonicFabs
  FnormalizeCanonic: float.
Hint Resolve nNrMMimLevNum: arith.
Hint Resolve FsubnormalFbounded FsubnormalFexp FsubnormalDigit: float.
Hint Resolve FcanonicBound: float.
