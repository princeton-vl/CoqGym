(****************************************************************************
                                                                             
          IEEE754  :  FroundMult                                                     
                                                                             
          Laurent Thery, Sylvie Boldo                                                      
                                                                             
  ******************************************************************************)
Require Export FroundProp.
 
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
 
Theorem errorBoundedMultMin :
 forall p q fmin : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 isMin b radix (p * q) fmin ->
 exists r : float,
   r = (p * q - fmin)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
intros p q fmin Fp Fq H' H'0 H'1 H'2.
cut (0 <= Fnum p * Fnum q)%Z;
 [ intros multPos
 | apply Zle_mult_gen; apply (LeR0Fnum radix); auto with arith ].
cut (ex (fun m : Z => FtoRradix fmin = Float m (Fexp (Fmult p q)))).
2: unfold FtoRradix in |- *;
    apply
     RoundedModeRep
      with (b := b) (precision := precision) (P := isMin b radix); 
    auto.
2: apply MinRoundedModeP with (precision := precision); auto.
2: rewrite (Fmult_correct radix); auto with zarith.
intros H'3; elim H'3; intros m E; clear H'3.
exists (Fminus radix (Fmult p q) (Float m (Fexp (Fmult p q)))).
split.
rewrite E; unfold FtoRradix in |- *; repeat rewrite Fminus_correct;
 repeat rewrite Fmult_correct; auto with zarith.
split.
cut (fmin <= Fmult p q)%R;
 [ idtac
 | unfold FtoRradix in |- *; rewrite Fmult_correct; auto; case H'2;
    auto with real zarith; (intros H1 H2; case H2; auto with zarith) ].
rewrite E; unfold Fmult, Fminus, Fopp, Fplus in |- *; simpl in |- *; auto.
repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse; auto.
simpl in |- *; repeat rewrite Zpower_nat_O; repeat rewrite Zmult_1_r.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
intros H'3;
 (cut (m <= Fnum p * Fnum q)%Z;
   [ idtac
   | apply le_IZR;
      apply Rmult_le_reg_l with (r := powerRZ radix (Fexp p + Fexp q));
      auto with real zarith;
      repeat rewrite (Rmult_comm (powerRZ radix (Fexp p + Fexp q)));
      auto with zarith ]); intros H'4.
repeat split; simpl in |- *; auto.
case (ZquotientProp (Fnum p * Fnum q) (Zpower_nat radix precision));
 auto with zarith.
intros x (H'5, (H'6, H'7)).
cut
 (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
  powerRZ radix (precision + (Fexp p + Fexp q)) <= fmin)%R;
 [ rewrite E; intros H'8 | idtac ].
cut
 (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
  powerRZ radix precision <= m)%R; [ intros H'9 | idtac ].
rewrite Zabs_eq; auto with zarith.
apply Zle_lt_trans with x; auto.
replace x with
 (Fnum p * Fnum q +
  -
  (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
   Zpower_nat radix precision))%Z.
apply Zplus_le_compat_l; auto.
apply Zle_Zopp.
apply le_IZR; auto.
rewrite Rmult_IZR.
rewrite Zpower_nat_Z_powerRZ; auto with zarith.
pattern (Fnum p * Fnum q)%Z at 1 in |- *; rewrite H'5; ring.
rewrite pGivesBound.
rewrite <- (Zabs_eq (Zpower_nat radix precision)); auto with zarith.
apply Zlt_Zabs_inv2; auto.
apply Rmult_le_reg_l with (r := powerRZ radix (Fexp p + Fexp q));
 auto with real zarith.
repeat rewrite (Rmult_comm (powerRZ radix (Fexp p + Fexp q))); auto.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
case
 (FboundedMbound _ radixMoreThanOne b precision)
  with
    (z := (precision + (Fexp p + Fexp q))%Z)
    (m := Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision));
 auto with zarith.
apply Zmult_le_reg_r with (p := Zpower_nat radix precision); auto with zarith.
apply Zlt_gt; auto with zarith.
pattern (Zpower_nat radix precision) at 2 in |- *;
 rewrite <- (fun x => Zabs_eq (Zpower_nat radix x)).
rewrite <- Zabs_Zmult.
apply Zle_trans with (1 := H'6); auto with zarith.
rewrite Zabs_Zmult.
apply Zle_trans with (Zpower_nat radix precision * Zabs (Fnum q))%Z.
apply Zle_Zmult_comp_r; auto with zarith.
apply Zlt_le_weak; rewrite <- pGivesBound; case Fp; auto with float.
apply Zle_Zmult_comp_l; auto with zarith.
apply Zlt_le_weak; rewrite <- pGivesBound; case Fq; auto with float.
auto with zarith.
intros x0 (H'8, H'9); rewrite <- H'9.
case H'2.
intros H'10 (H'11, H'12); apply H'12; auto.
rewrite H'9; auto.
rewrite powerRZ_add; auto with real zarith.
rewrite <- Rmult_assoc.
unfold FtoRradix in |- *; rewrite <- Fmult_correct; auto with zarith.
unfold Fmult, FtoR in |- *; simpl in |- *.
repeat rewrite (fun x => Rmult_comm x (powerRZ radix (Fexp p + Fexp q))).
apply Rmult_le_compat_l; auto with real zarith.
rewrite <- Zpower_nat_Z_powerRZ; auto with zarith.
pattern (Fnum p * Fnum q)%Z at 2 in |- *;
 rewrite <- (Zabs_eq (Fnum p * Fnum q)); auto.
rewrite <- Rmult_IZR; apply Rle_IZR; apply Zle_Zabs_inv2; auto.
simpl in |- *; auto.
apply Zmin_n_n; auto.
Qed.
 
Theorem errorBoundedMultMax :
 forall p q fmax : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 isMax b radix (p * q) fmax ->
 exists r : float,
   FtoRradix r = (p * q - fmax)%R /\
   Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
intros p q fmax Fp Fq H' H'0 H'1 H'2.
cut (0 <= Fnum p * Fnum q)%Z;
 [ intros multPos
 | apply Zle_mult_gen; apply (LeR0Fnum radix); auto with arith ].
case (ZquotientProp (Fnum p * Fnum q) (Zpower_nat radix precision));
 auto with zarith.
intros r; intros (H'3, (H'4, H'5)).
cut (0 <= Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision))%Z;
 [ intros Z2 | apply ZquotientPos; auto with zarith ].
cut (0 <= r)%Z;
 [ intros Z3
 | replace r with
    (Fnum p * Fnum q -
     Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
     Zpower_nat radix precision)%Z;
    [ idtac | pattern (Fnum p * Fnum q)%Z at 1 in |- *; rewrite H'3; ring ];
    auto ].
2: apply Zle_Zminus_ZERO; rewrite Zabs_eq in H'4; auto with zarith;
    rewrite Zabs_eq in H'4; auto with zarith.
case (Z_eq_dec r 0); intros Z4.
exists (Fzero (Fexp p + Fexp q)); repeat (split; auto with float).
replace (FtoRradix (Fzero (Fexp p + Fexp q))) with 0%R;
 [ idtac | unfold Fzero, FtoRradix, FtoR in |- *; simpl in |- *; ring ].
apply Rplus_eq_reg_l with (r := FtoRradix fmax).
replace (fmax + 0)%R with (FtoRradix fmax); [ idtac | ring ].
replace (fmax + (p * q - fmax))%R with (p * q)%R; [ idtac | ring ].
unfold FtoRradix in |- *; rewrite <- (Fmult_correct radix); auto with zarith.
case
 (FboundedMbound _ radixMoreThanOne b precision)
  with
    (z := (precision + (Fexp p + Fexp q))%Z)
    (m := Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision));
 auto with zarith.
apply Zmult_le_reg_r with (p := Zpower_nat radix precision); auto with zarith.
apply Zlt_gt; auto with zarith.
pattern (Zpower_nat radix precision) at 2 in |- *;
 rewrite <- (fun x => Zabs_eq (Zpower_nat radix x)).
rewrite <- Zabs_Zmult.
apply Zle_trans with (1 := H'4); auto with zarith.
rewrite Zabs_Zmult.
apply Zle_trans with (Zpower_nat radix precision * Zabs (Fnum q))%Z.
apply Zle_Zmult_comp_r; auto with zarith.
apply Zlt_le_weak; rewrite <- pGivesBound; case Fp; auto with float.
apply Zle_Zmult_comp_l; auto with zarith.
apply Zlt_le_weak; rewrite <- pGivesBound; case Fq; auto with float.
auto with zarith.
intros x (H'6, H'7).
cut (FtoR radix (Fmult p q) = FtoR radix x).
intros H'8; rewrite H'8.
apply sym_eq; apply (ProjectMax b radix); auto.
rewrite <- H'8; auto.
rewrite Fmult_correct; auto with zarith.
rewrite H'7.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_add with (n := Z_of_nat precision); auto with real zarith.
pattern (Fnum p * Fnum q)%Z at 1 in |- *; rewrite H'3.
rewrite plus_IZR; rewrite Rmult_IZR.
repeat rewrite Zpower_nat_Z_powerRZ; auto with real zarith.
rewrite Z4; simpl;ring.
cut (ex (fun m : Z => FtoRradix fmax = Float m (Fexp (Fmult p q))));
 [ intros Z5 | idtac ].
2: unfold FtoRradix in |- *;
    apply
     RoundedModeRep
      with (b := b) (precision := precision) (P := isMax b radix); 
    auto.
2: apply MaxRoundedModeP with (precision := precision); auto.
2: rewrite (Fmult_correct radix); auto with zarith.
elim Z5; intros m E; clear Z5.
exists (Fopp (Fminus radix (Float m (Fexp (Fmult p q))) (Fmult p q))).
split.
rewrite E; unfold FtoRradix in |- *; repeat rewrite Fopp_correct;
 repeat rewrite Fminus_correct; repeat rewrite Fmult_correct;
 auto with zarith; ring.
cut
 (Fexp (Fopp (Fminus radix (Float m (Fexp (Fmult p q))) (Fmult p q))) =
  (Fexp p + Fexp q)%Z); [ intros Z5 | idtac ].
split; auto.
split; [ idtac | rewrite Z5; auto ].
cut (Fmult p q <= fmax)%R;
 [ idtac
 | unfold FtoRradix in |- *; rewrite Fmult_correct; auto; case H'2;
    auto with real zarith; (intros H1 H2; case H2; auto) ].
cut
 (fmax <=
  Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)) *
  powerRZ radix (precision + (Fexp p + Fexp q)))%R.
rewrite E; repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse;
 repeat rewrite Zpower_nat_O; repeat rewrite Zmult_1_r; 
 auto.
unfold Fmult, Fminus, Fplus, Fopp in |- *; simpl in |- *.
repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse;
 repeat rewrite Zpower_nat_O; repeat rewrite Zmult_1_r; 
 auto.
intros H1 H2; rewrite Zabs_Zopp; apply Zlt_Zabs_intro.
apply Zlt_le_trans with 0%Z; auto with zarith.
cut (Fnum p * Fnum q <= m)%Z; auto with zarith.
apply le_IZR;
 apply (Rle_monotony_contra_exp radix) with (z := (Fexp p + Fexp q)%Z);
 auto with zarith.
cut
 (m <=
  Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)) *
  Zpower_nat radix precision)%Z; [ intros H'9 | idtac ].
apply Zle_lt_trans with (Zpower_nat radix precision - r)%Z;
 [ idtac | rewrite pGivesBound; auto with zarith ].
replace r with
 (Fnum p * Fnum q -
  Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
  Zpower_nat radix precision)%Z.
replace
 (Zpower_nat radix precision -
  (Fnum p * Fnum q -
   Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
   Zpower_nat radix precision))%Z with
 (Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)) *
  Zpower_nat radix precision - Fnum p * Fnum q)%Z; 
 auto with zarith.
unfold Zsucc in |- *; simpl in |- *; ring.
pattern (Fnum p * Fnum q)%Z at 1 in |- *; rewrite H'3; ring.
apply le_IZR;
 apply (Rle_monotony_contra_exp radix) with (z := (Fexp p + Fexp q)%Z);
 auto with zarith.
replace
 (IZR
    (Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)) *
     Zpower_nat radix precision) * powerRZ radix (Fexp p + Fexp q))%R with
 (Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)) *
  powerRZ radix (precision + (Fexp p + Fexp q)))%R; 
 [ auto | idtac ].
rewrite powerRZ_add; auto with real zarith.
repeat rewrite Rmult_IZR; repeat rewrite Zpower_nat_Z_powerRZ; auto with zarith.
ring.
case
 (FboundedMbound _ radixMoreThanOne b precision)
  with
    (z := (precision + (Fexp p + Fexp q))%Z)
    (m := Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)));
 auto with arith.
rewrite Zabs_eq; auto with zarith.
apply Zlt_le_succ.
case (Zle_lt_or_eq _ _ multPos); intros Eq1.
cut (0 < Zabs (Fnum p))%Z; [ intros Eq2 | idtac ].
cut (0 < Zabs (Fnum q))%Z; [ intros Eq3 | idtac ].
apply Zlt_mult_simpl_l with (c := Zpower_nat radix precision);
 auto with zarith.
rewrite (fun x y z => Zmult_comm x (Zquotient y z)).
apply Zle_lt_trans with (Fnum p * Fnum q)%Z.
rewrite Zabs_eq in H'4; auto with zarith; rewrite Zabs_eq in H'4;
 auto with zarith.
rewrite <- (Zabs_eq (Fnum p * Fnum q)); auto with zarith; rewrite Zabs_Zmult.
apply Zlt_trans with (Zabs (Fnum p) * Zpower_nat radix precision)%Z.
cut (Zabs (Fnum q) < Zpower_nat radix precision)%Z;
 [ intros Eq4; apply Zmult_gt_0_lt_compat_l
 | rewrite <- pGivesBound; case Fq ]; auto with zarith.
cut (Zabs (Fnum p) < Zpower_nat radix precision)%Z;
 [ intros Eq4; apply Zmult_gt_0_lt_compat_r
 | rewrite <- pGivesBound; case Fp ]; auto with zarith.
case (Zle_lt_or_eq _ _ (Zle_ZERO_Zabs (Fnum q))); auto.
intros Eq3; Contradict Eq1; replace (Fnum q) with 0%Z; auto with zarith.
generalize Eq3; case (Fnum q); simpl in |- *; auto; intros; discriminate.
case (Zle_lt_or_eq _ _ (Zle_ZERO_Zabs (Fnum p))); auto.
intros Eq3; Contradict Eq1; replace (Fnum p) with 0%Z; auto with zarith.
generalize Eq3; case (Fnum p); simpl in |- *; auto; intros; discriminate.
rewrite <- Eq1; replace (Zquotient 0 (Zpower_nat radix precision)) with 0%Z;
 auto with zarith.
apply Zle_trans with (1 := H'1); auto with zarith.
intros f1 (Hf1, Hf2); rewrite <- Hf2.
case H'2; intros L1 (L2, L3); apply L3; auto.
rewrite Hf2; unfold Fmult, FtoRradix, FtoR in |- *.
replace
 (Fnum p * powerRZ radix (Fexp p) * (Fnum q * powerRZ radix (Fexp q)))%R with
 (Fnum p * Fnum q * powerRZ radix (Fexp p + Fexp q))%R.
replace
 (Zsucc (Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision)) *
  powerRZ radix (precision + (Fexp p + Fexp q)))%R with
 ((Zquotient (Fnum p * Fnum q) (Zpower_nat radix precision) *
   Zpower_nat radix precision + Zpower_nat radix precision)%Z *
  powerRZ radix (Fexp p + Fexp q))%R.
apply Rle_monotone_exp; auto with real zarith.
rewrite <- Rmult_IZR; apply Rle_IZR.
pattern (Fnum p * Fnum q)%Z at 1 in |- *; rewrite H'3;
 cut (r < Zpower_nat radix precision)%Z; auto with zarith.
rewrite Zabs_eq in H'5; auto with zarith; rewrite Zabs_eq in H'5;
 auto with zarith.
unfold Zsucc in |- *; repeat rewrite Rmult_IZR || rewrite plus_IZR;
 simpl in |- *.
rewrite (powerRZ_add radix precision); auto with real zarith;
 rewrite <- (Zpower_nat_Z_powerRZ radix precision); auto with real zarith; 
 ring.
rewrite powerRZ_add; auto with real zarith; ring.
unfold Fopp, Fminus, Fmult in |- *; simpl in |- *; auto.
apply Zmin_n_n.
Qed.
 
Theorem multExpMin :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p * q)%R pq ->
 exists s : float,
   Fbounded b s /\ s = pq :>R /\ (Fexp p + Fexp q <= Fexp s)%Z.
intros P H' p q pq H'0.
case
 (RoundedModeRep b radix precision) with (p := Fmult p q) (q := pq) (P := P);
 auto with zarith.
rewrite Fmult_correct; auto with zarith.
simpl in |- *; intros x H'1.
case
 (eqExpLess _ radixMoreThanOne b)
  with (p := pq) (q := Float x (Fexp (Fmult p q))); 
 auto.
apply RoundedModeBounded with (radix := radix) (P := P) (r := (p * q)%R);
 auto.
simpl in |- *; intros x0 H'2; elim H'2; intros H'3 H'4; elim H'4;
 intros H'5 H'6; clear H'4 H'2.
exists x0; split; [ idtac | split ]; auto.
unfold FtoRradix in |- *; rewrite H'5; auto.
apply le_IZR; auto.
Qed.
 
Theorem multExpUpperBound :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p * q)%R pq ->
 Fbounded b p ->
 Fbounded b q ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 exists r : float,
   Fbounded b r /\ r = pq :>R /\ (Fexp r <= precision + (Fexp p + Fexp q))%Z.
intros P H' p q pq H'0 H'1 H'2 H'3.
replace (precision + (Fexp p + Fexp q))%Z with
 (Fexp (Float (pPred (vNum b)) (precision + (Fexp p + Fexp q))));
 [ idtac | simpl in |- *; auto ].
unfold FtoRradix in |- *; apply eqExpMax; auto.
apply RoundedModeBounded with (radix := radix) (P := P) (r := (p * q)%R);
 auto; auto.
unfold pPred in |- *; apply maxFbounded; auto.
apply Zle_trans with (1 := H'3); auto with zarith.
replace (FtoR radix (Float (pPred (vNum b)) (precision + (Fexp p + Fexp q))))
 with (radix * Float (pPred (vNum b)) (pred precision + (Fexp p + Fexp q)))%R.
rewrite Fabs_correct; auto with zarith.
unfold FtoRradix in |- *;
 apply
  RoundedModeMultAbs
   with (b := b) (precision := precision) (P := P) (r := (p * q)%R); 
 auto.
unfold pPred in |- *; apply maxFbounded; auto with zarith.
rewrite Rabs_mult; auto.
apply
 Rle_trans
  with
    (FtoR radix
       (Fmult (Float (pPred (vNum b)) (Fexp p))
          (Float (pPred (vNum b)) (Fexp q)))).
rewrite Fmult_correct; auto with arith.
apply Rmult_le_compat; auto with real.
rewrite <- (Fabs_correct radix); try apply maxMax1; auto with zarith.
rewrite <- (Fabs_correct radix); try apply maxMax1; auto with zarith.
unfold Fmult, FtoR in |- *; simpl in |- *; auto.
rewrite powerRZ_add with (n := Z_of_nat (pred precision));
 auto with real arith.
repeat rewrite <- Rmult_assoc.
repeat rewrite (fun (z : Z) (x : R) => Rmult_comm x (powerRZ radix z));
 auto.
apply Rmult_le_compat_l; auto with real arith.
rewrite <- Rmult_assoc.
rewrite (fun x : R => Rmult_comm x radix).
rewrite <- powerRZ_Zs; auto with real arith.
replace (Zsucc (pred precision)) with (Z_of_nat precision).
rewrite Rmult_IZR; auto.
apply Rmult_le_compat; auto with real arith.
replace 0%R with (IZR 0); unfold pPred in |- *; try apply Rle_IZR;
 auto with real zarith.
replace 0%R with (IZR 0); unfold pPred in |- *; try apply Rle_IZR;
 auto with real zarith.
unfold pPred in |- *; rewrite pGivesBound; rewrite <- Zpower_nat_Z_powerRZ;
 auto with real zarith.
rewrite inj_pred; auto with arith zarith.
auto with real zarith.
auto with real zarith.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
repeat rewrite (Rmult_comm (pPred (vNum b))).
rewrite <- Rmult_assoc.
rewrite <- powerRZ_Zs; auto with real zarith.
rewrite inj_pred; auto with arith zarith.
replace (Zsucc (Zpred precision + (Fexp p + Fexp q))) with
 (precision + (Fexp p + Fexp q))%Z; auto; unfold Zsucc, Zpred in |- *; 
 ring.
Qed.
 
Theorem errorBoundedMultPos :
 forall P,
 RoundedModeP b radix P ->
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 P (p * q)%R f ->
 exists r : float,
   r = (p * q - f)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
intros P H p q f H0 H1 H2 H3 H4 H5.
generalize errorBoundedMultMin errorBoundedMultMax; intros H6 H7.
cut (MinOrMaxP b radix P);
 [ intros | case H; intros H'1 (H'2, (H'3, H'4)); auto ].
case (H8 (p * q)%R f); auto.
Qed.
 
Theorem errorBoundedMultNeg :
 forall P,
 RoundedModeP b radix P ->
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 (p <= 0)%R ->
 (0 <= q)%R ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 P (p * q)%R f ->
 exists r : float,
   r = (p * q - f)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
intros P H p q f H0 H1 H2 H3 H4 H5.
generalize errorBoundedMultMin errorBoundedMultMax; intros H6 H7.
cut (MinOrMaxP b radix P);
 [ intros | case H; intros H'1 (H'2, (H'3, H'4)); auto ].
case (H8 (p * q)%R f); auto; intros H9.
generalize (H7 (Fopp p) q (Fopp f)); intros H12.
lapply H12; auto with float; intros H10; clear H12.
lapply H10; auto; intros H12; clear H10.
lapply H12;
 [ intros H10
 | unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real ];
 clear H12.
lapply H10; auto; intros H12; clear H10.
lapply H12; [ intros H10 | simpl in |- *; auto ]; clear H12.
lapply H10; [ intros H12 | idtac ]; clear H10.
2: replace (Fopp p * q)%R with (- (p * q))%R;
    [ apply MinOppMax; auto | idtac ].
2: unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
elim H12; intros r H10; clear H12; elim H10; intros H11 H12; clear H10.
elim H12; clear H12; intros H10 H12.
exists (Fopp r); split; [ generalize H11 | split; auto with float ].
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; intros H13;
 rewrite H13; ring.
generalize (H6 (Fopp p) q (Fopp f)); intros H12.
lapply H12; auto with float; intros H10; clear H12.
lapply H10; auto; intros H12; clear H10.
lapply H12;
 [ intros H10
 | unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real ];
 clear H12.
lapply H10; auto; intros H12; clear H10.
lapply H12; [ intros H10 | simpl in |- *; auto ]; clear H12.
lapply H10; [ intros H12 | idtac ]; clear H10.
2: replace (Fopp p * q)%R with (- (p * q))%R;
    [ apply MaxOppMin; auto | idtac ].
2: unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
elim H12; intros r H10; clear H12; elim H10; intros H11 H12; clear H10.
elim H12; clear H12; intros H10 H12.
exists (Fopp r); split; [ generalize H11 | split; auto with float ].
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; intros H13;
 rewrite H13; ring.
Qed.
 
Theorem errorBoundedMult :
 forall P,
 RoundedModeP b radix P ->
 forall p q f : float,
 Fbounded b p ->
 Fbounded b q ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 P (p * q)%R f ->
 exists r : float,
   r = (p * q - f)%R :>R /\ Fbounded b r /\ Fexp r = (Fexp p + Fexp q)%Z.
intros P H p q f H0 H1 H2 H3.
case (Rle_or_lt 0 p); intros H4; case (Rle_or_lt 0 q); intros H5.
apply errorBoundedMultPos with P; auto.
replace (Fexp p) with (Fexp (Fopp p)); auto with float.
replace (Fexp q) with (Fexp (Fopp q)); auto with float.
cut ((p * q)%R = (Fopp p * Fopp q)%R); [ intros H6; rewrite H6 | idtac ].
apply errorBoundedMultNeg with P; auto with float real.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
rewrite <- H6; auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; ring.
apply errorBoundedMultNeg with P; auto with float real.
replace (Fexp p) with (Fexp (Fopp p)); auto with float.
replace (Fexp q) with (Fexp (Fopp q)); auto with float.
cut ((p * q)%R = (Fopp p * Fopp q)%R); [ intros H6; rewrite H6 | idtac ].
apply errorBoundedMultPos with P; auto with float real.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
rewrite <- H6; auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; ring.
Qed.
 
Theorem errorBoundedMultExp_aux :
 forall n1 n2 : Z,
 (Zabs n1 < Zpos (vNum b))%Z ->
 (Zabs n2 < Zpos (vNum b))%Z ->
 (exists ny : Z,
    (exists ey : Z,
       (n1 * n2)%R = (ny * powerRZ radix ey)%R :>R /\
       (Zabs ny < Zpos (vNum b))%Z)) ->
 exists nx : Z,
   (exists ex : Z,
      (n1 * n2)%R = (nx * powerRZ radix ex)%R :>R /\
      (Zabs nx < Zpos (vNum b))%Z /\
      (0 <= ex)%Z /\ (ex <= precision)%Z).
intros n1 n2 H H0 H1.
case H1; intros ny (ey, (H2, H3)).
case (Zle_or_lt 0 ey); intros Zl1.
case (Zle_or_lt ey precision); intros Zl2.
exists ny; exists ey; repeat (split; auto).
exists (ny * Zpower_nat radix (Zabs_nat (ey - precision)))%Z;
 exists (Z_of_nat precision); repeat (split; auto with zarith).
replace (IZR (ny * Zpower_nat radix (Zabs_nat (ey - precision)))) with
 (ny * powerRZ radix (ey - precision))%R.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with zarith real.
replace (ey - precision + precision)%Z with ey; [ auto | ring ].
rewrite Rmult_IZR.
rewrite Zpower_nat_powerRZ_absolu; auto with real zarith.
rewrite Zabs_Zmult.
apply lt_IZR; apply Rmult_lt_reg_l with (r := powerRZ radix precision);
 auto with real zarith.
repeat rewrite (fun x y => Rmult_comm (powerRZ x y)).
rewrite Rmult_IZR.
rewrite Rmult_assoc.
rewrite (Zabs_eq (Zpower_nat radix (Zabs_nat (ey - precision))));
 auto with zarith.
rewrite Zpower_nat_powerRZ_absolu; auto with real zarith.
rewrite <- powerRZ_add; auto with real zarith.
replace (ey - precision + precision)%Z with ey; [ idtac | ring ].
replace (powerRZ radix precision) with (IZR (Zpos (vNum b)));
 [ idtac
 | rewrite pGivesBound; rewrite <- Zpower_nat_powerRZ_absolu;
    try rewrite absolu_INR; auto with zarith ].
rewrite <- (fun x y => Rabs_pos_eq (powerRZ x y)); auto with real zarith.
rewrite <- Faux.Rabsolu_Zabs; rewrite <- Rabs_mult; rewrite <- H2.
rewrite Rabs_mult; repeat rewrite Faux.Rabsolu_Zabs; auto with real zarith.
case (Zle_lt_or_eq 0 (Zabs n2)); auto with zarith; intros Z1.
apply Rlt_trans with (Zpos (vNum b) * Zabs n2)%R;
 auto with real zarith.
rewrite <- Z1; auto with real zarith.
replace (Zabs n1 * 0%Z)%R with (0 * Zpos (vNum b))%R;
 [ auto with real zarith | simpl; ring ].
exists (n1 * n2)%Z; exists 0%Z; repeat (split; auto with zarith).
rewrite Rmult_IZR; rewrite powerRZ_O; ring.
apply lt_IZR.
rewrite <- Faux.Rabsolu_Zabs; rewrite Rmult_IZR; rewrite H2.
rewrite Rabs_mult.
apply Rle_lt_trans with (Rabs ny).
pattern (Rabs ny) at 2 in |- *; replace (Rabs ny) with (Rabs ny * 1)%R;
 [ apply Rmult_le_compat_l | ring ]; auto with arith real.
rewrite (Rabs_pos_eq (powerRZ radix ey));
 [ idtac | apply powerRZ_le; auto with arith real ].
replace 1%R with (powerRZ radix 0); [ apply Rle_powerRZ | simpl in |- * ];
 auto with real arith zarith.
rewrite Faux.Rabsolu_Zabs; auto with real zarith.
Qed.
 
Theorem errorBoundedMultExpPos :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 (0 <= p)%R ->
 (0 <= q)%R ->
 P (p * q)%R pq ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fbounded b r /\
       Fbounded b s /\
       r = pq :>R /\
       s = (p * q - r)%R :>R /\
       Fexp s = (Fexp p + Fexp q)%Z :>Z /\
       (Fexp s <= Fexp r)%Z /\ (Fexp r <= precision + (Fexp p + Fexp q))%Z)).
intros P H p q pq H0 H1 H2 H3 H4 H5.
case (multExpUpperBound P H p q pq); auto; intros r (H'1, (H'2, H'3)).
case (Req_dec (p * q - pq) 0); intros H6.
case (Req_dec pq 0); intros H7.
cut (Fbounded b (Fzero (Fexp p + Fexp q))); [ intros Fb1 | idtac ].
exists (Fzero (Fexp p + Fexp q)); exists (Fzero (Fexp p + Fexp q));
 repeat (split; simpl in |- *; auto with zarith).
rewrite H7; unfold FtoRradix in |- *; apply FzeroisReallyZero.
unfold FtoRradix in |- *; rewrite FzeroisReallyZero; rewrite <- H7.
pattern (FtoRradix pq) at 1 in |- *; rewrite H7; auto with real.
repeat (split; auto); simpl in |- *; auto with arith zarith.
case (errorBoundedMultExp_aux (Fnum p) (Fnum q)); auto with float real zarith.
exists (Fnum pq); exists (Fexp pq - (Fexp p + Fexp q))%Z; split.
apply Rmult_eq_reg_l with (powerRZ radix (Fexp p + Fexp q));
 auto with real zarith.
repeat rewrite (fun x y => Rmult_comm (powerRZ x y)).
apply trans_eq with (p * q)%R; auto.
rewrite <- (Fmult_correct radix); auto with real zarith;
 unfold FtoRradix, FtoR, Fmult in |- *; simpl in |- *; 
 rewrite Rmult_IZR; auto.
apply trans_eq with (FtoRradix pq); auto with real.
rewrite Rmult_assoc; rewrite <- powerRZ_add; auto with real zarith.
replace (Fexp pq - (Fexp p + Fexp q) + (Fexp p + Fexp q))%Z with (Fexp pq);
 auto; ring.
cut (Fbounded b pq); [ intros Z1; case Z1 | idtac ]; auto with real zarith.
apply (RoundedModeBounded b radix P (p * q)); auto.
intros nx (ex, (H'4, (H'5, (H'6, H'7)))).
cut (FtoRradix pq = FtoRradix (Float nx (ex + (Fexp p + Fexp q))) :>R);
 [ intros Eq1 | idtac ].
exists (Float nx (ex + (Fexp p + Fexp q))); exists (Fzero (Fexp p + Fexp q));
 repeat (split; simpl in |- *; auto with real zarith).
rewrite <- Eq1; rewrite H6; apply (FzeroisReallyZero radix).
replace (FtoRradix pq) with (p * q)%R.
unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *.
rewrite powerRZ_add; auto with zarith real.
repeat rewrite <- Rmult_assoc; rewrite <- H'4; rewrite powerRZ_add;
 [ ring | auto with zarith real ].
replace (FtoRradix p * FtoRradix q)%R with
 (pq + (FtoRradix p * FtoRradix q - FtoRradix pq))%R; 
 [ rewrite H6 | idtac ]; ring.
case (errorBoundedMultPos P H p q pq); auto.
intros s (H'4, (H'5, H'6)).
exists r; exists s; repeat (split; auto with zarith).
rewrite H'2; auto.
apply Zlt_le_weak;
 apply RoundedModeErrorExpStrict with b radix precision P (p * q)%R; 
 auto.
cut (CompatibleP b radix P);
 [ intros H'7 | case H; try intros H'7 (H'8, (H'9, H'10)); auto ].
apply H'7 with (p * q)%R pq; auto with real.
fold FtoRradix in |- *; rewrite H'2; auto with real.
fold FtoRradix in |- *; rewrite H'4; auto with real.
Qed.
 
Theorem errorBoundedMultExp :
 forall P, (RoundedModeP b radix P) -> 
 forall p q pq : float,
  (Fbounded b p) -> (Fbounded b q) ->
  (P (p * q)%R pq) ->
   (-(dExp b) <= Fexp p + Fexp q)%Z ->
   exists r : float,
   exists s : float,
      (Fbounded b r) /\ (Fbounded b s) /\
       r = pq :>R /\ s = (p * q - r)%R :>R /\
       (Fexp s =  Fexp p + Fexp q)%Z /\
       (Fexp s <= Fexp r)%Z /\ 
       (Fexp r <= precision + (Fexp p + Fexp q))%Z.
intros P H p q pq H1 H2 H3 H4.
cut (MinOrMaxP b radix P);
 [ intros | case H; intros H'1 (H'2, (H'3, H'4)); auto ].
case H0 with (p*q)%R pq; auto; intros H0'; clear H0.
case (Rle_or_lt 0 p); intros Rl1.
case (Rle_or_lt 0 q); intros Rl2.
apply (errorBoundedMultExpPos P); auto.
case errorBoundedMultExpPos with (isMax b radix) p (Fopp q) (Fopp pq); auto with float real.
apply MaxRoundedModeP with precision; auto.
rewrite (Fopp_correct radix); auto with real.
replace (FtoRradix p * FtoRradix (Fopp q))%R with
 (- (FtoRradix p * FtoRradix q))%R; [apply MinOppMax;auto|idtac].
rewrite (Fopp_correct radix);
 fold FtoRradix in |- *; auto with zarith; ring.
intros r (s, (H5, (H6, (H7, (H8, H9))))); exists (Fopp r); exists (Fopp s);
 repeat (split; simpl in |- *; auto with float real zarith).
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H7; repeat rewrite (Fopp_correct radix); auto with zarith;
 fold FtoRradix; ring.
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H8; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix; ring.
case (Rle_or_lt 0 q); intros Rl2.
case errorBoundedMultExpPos with (isMax b radix) (Fopp p) q (Fopp pq); auto with float real.
apply MaxRoundedModeP with precision; auto.
rewrite (Fopp_correct radix); auto with real.
replace (FtoRradix (Fopp p) * FtoRradix q)%R with
 (- (FtoRradix p * FtoRradix q))%R; [apply MinOppMax;auto|idtac].
rewrite (Fopp_correct radix);
 fold FtoRradix in |- *; auto with zarith; ring.
intros r (s, (H5, (H6, (H7, (H8, H9))))); exists (Fopp r); exists (Fopp s);
 repeat (split; simpl in |- *; auto with float real zarith).
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H7; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix; ring.
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H8; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix;ring.
case (errorBoundedMultExpPos P H (Fopp p) (Fopp q) pq); auto with float real.
rewrite (Fopp_correct radix); auto with real.
rewrite (Fopp_correct radix); auto with real.
replace (FtoRradix (Fopp p) * FtoRradix (Fopp q))%R with
 (FtoRradix p * FtoRradix q)%R; auto; repeat rewrite (Fopp_correct radix);
 fold FtoRradix in |- *; auto with zarith; ring.
intros r (s, (H5, (H6, (H7, (H8, (H9, (H10, H11))))))); exists r; exists s;
 repeat (split; simpl in |- *; auto with float real zarith).
fold FtoRradix in |- *; rewrite H8; repeat rewrite (Fopp_correct radix);
 auto with zarith; fold FtoRradix; ring.
case (Rle_or_lt 0 p); intros Rl1.
case (Rle_or_lt 0 q); intros Rl2.
apply (errorBoundedMultExpPos P); auto.
case errorBoundedMultExpPos with (isMin b radix) p (Fopp q) (Fopp pq); auto with float real.
apply MinRoundedModeP with precision; auto.
rewrite (Fopp_correct radix); auto with real.
replace (FtoRradix p * FtoRradix (Fopp q))%R with
 (- (FtoRradix p * FtoRradix q))%R; [apply MaxOppMin;auto|idtac].
rewrite (Fopp_correct radix);
 fold FtoRradix in |- *; auto with zarith; ring.
intros r (s, (H5, (H6, (H7, (H8, H9))))); exists (Fopp r); exists (Fopp s);
 repeat (split; simpl in |- *; auto with float real zarith).
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H7; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix; ring.
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H8; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix; ring.
case (Rle_or_lt 0 q); intros Rl2.
case errorBoundedMultExpPos with (isMin b radix) (Fopp p) q (Fopp pq); auto with float real.
apply MinRoundedModeP with precision; auto.
rewrite (Fopp_correct radix); auto with real.
replace (FtoRradix (Fopp p) * FtoRradix q)%R with
 (- (FtoRradix p * FtoRradix q))%R; [apply MaxOppMin;auto|idtac].
rewrite (Fopp_correct radix);
 fold FtoRradix in |- *; auto with zarith; ring.
intros r (s, (H5, (H6, (H7, (H8, H9))))); exists (Fopp r); exists (Fopp s);
 repeat (split; simpl in |- *; auto with float real zarith).
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H7; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix; ring.
repeat rewrite (Fopp_correct radix); auto with zarith; fold FtoRradix in |- *;
 rewrite H8; repeat rewrite (Fopp_correct radix); auto with zarith; 
 fold FtoRradix;ring.
case (errorBoundedMultExpPos P H (Fopp p) (Fopp q) pq); auto with float real.
rewrite (Fopp_correct radix); auto with real.
rewrite (Fopp_correct radix); auto with real.
replace (FtoRradix (Fopp p) * FtoRradix (Fopp q))%R with
 (FtoRradix p * FtoRradix q)%R; auto; repeat rewrite (Fopp_correct radix);
 fold FtoRradix in |- *; auto with zarith; ring.
intros r (s, (H5, (H6, (H7, (H8, (H9, (H10, H11))))))); exists r; exists s;
 repeat (split; simpl in |- *; auto with float real zarith).
fold FtoRradix in |- *; rewrite H8; repeat rewrite (Fopp_correct radix);
 auto with zarith; fold FtoRradix; ring.
Qed.
 
End FRoundP.
