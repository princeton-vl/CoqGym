(****************************************************************************
                                                                             
          IEEE754  :  ClosestMult                                                 
                                                                             
          Laurent Thery, Sylvie Boldo                                                      
                                                                             
  ******************************************************************************)
Require Export FroundMult.
Require Export ClosestProp.
Section FRoundP.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem closestLessMultPos :
 forall (p : float) (r : R),
 Closest b radix r p -> (0 <= r)%R -> (p <= 2%nat * r)%R.
intros p r H' H'0.
case ClosestMinOrMax with (1 := H'); intros H'3.
apply Rle_trans with r; auto with real.
apply isMin_inv1 with (1 := H'3).
case (MinEx b radix precision) with (r := r); auto with arith.
intros min Hmin.
apply Rle_trans with (min + p)%R; auto with real.
apply Rplus_le_reg_l with (r := (- p)%R).
replace (- p + p)%R with 0%R; [ idtac | ring ].
replace (- p + (min + p))%R with (FtoRradix min);
 [ apply (RleMinR0 b radix precision) with (r := r); auto | ring ].
apply Rplus_le_reg_l with (r := (- r)%R).
apply Rplus_le_reg_l with (r := (- min)%R).
replace (- min + (- r + (min + p)))%R with (Rabs (p - r)).
replace (- min + (- r + 2%nat * r))%R with (Rabs (min - r)).
case H'.
intros H'1 H'2; apply H'2; auto.
case Hmin; auto.
rewrite Faux.Rabsolu_left1; simpl in |- *.
ring; auto.
apply Rle_minus; apply isMin_inv1 with (1 := Hmin).
rewrite Rabs_right; simpl in |- *.
ring; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
replace (r + 0)%R with r; [ idtac | ring ].
replace (r + (p - r))%R with (FtoRradix p);
 [ apply isMax_inv1 with (1 := H'3) | ring ].
Qed.
 
Theorem closestLessMultNeg :
 forall (p : float) (r : R),
 Closest b radix r p -> (r <= 0)%R -> (2%nat * r <= p)%R.
intros p r H' H'0.
replace (2%nat * r)%R with (- (2%nat * - r))%R; [ idtac | ring ].
replace (FtoRradix p) with (- - p)%R;
 [ unfold FtoRradix in |- *; rewrite <- Fopp_correct | ring ].
apply Ropp_le_contravar.
apply closestLessMultPos; auto.
apply ClosestOpp; auto.
replace 0%R with (-0)%R; [ auto with real | ring ].
Qed.
 
Theorem closestLessMultAbs :
 forall (p : float) (r : R),
 Closest b radix r p -> (Rabs p <= 2%nat * Rabs r)%R.
intros p r H'; case (Rle_or_lt 0 r); intros H'1.
repeat rewrite Rabs_right; auto with real.
apply closestLessMultPos; auto.
apply Rle_ge;
 apply (RleRoundedR0 b radix precision) with (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
repeat rewrite Faux.Rabsolu_left1; auto.
replace (2%nat * - r)%R with (- (2%nat * r))%R;
 [ apply Ropp_le_contravar | ring ].
apply closestLessMultNeg; auto.
apply Rlt_le; auto.
apply Rlt_le; auto.
apply
 (RleRoundedLessR0 b radix precision) with (P := Closest b radix) (r := r);
 auto.
apply ClosestRoundedModeP with (precision := precision); auto.
apply Rlt_le; auto.
Qed.
 
Theorem errorBoundedMultClosest_aux :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p * q) pq ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 (p * q - pq)%R <> 0%R :>R ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fcanonic radix b r /\
       Fbounded b r /\
       Fbounded b s /\
       r = pq :>R /\
       s = (p * q - r)%R :>R /\
       Fexp s = (Fexp p + Fexp q)%Z :>Z /\
       (Fexp s <= Fexp r)%Z /\ (Fexp r <= precision + (Fexp p + Fexp q))%Z)).
intros p q pq Hp Hq H1 H2 H3.
cut (RoundedModeP b radix (Closest b radix));
 [ intros H4 | apply ClosestRoundedModeP with precision; auto ].
lapply (errorBoundedMultExp b radix precision);
 [ intros H'2; lapply H'2;
    [ intros H'3; lapply H'3;
       [ intros H'4; lapply (H'4 (Closest b radix));
             [ intros H'7; elim (H'7 p q pq);
                [ intros r E; elim E; intros s E0; elim E0; intros H'15 H'16;
                   elim H'16; intros H'17 H'18; elim H'18; 
                   intros H'19 H'20; elim H'20; intros H'21 H'22; 
                   elim H'22; intros H'23 H'24; elim H'24; 
                   intros H'25 H'26;
                   clear H'24 H'22 H'20 H'18 H'16 E0 E H'3 H'2
                | clear  H'3 H'2
                | clear  H'3 H'2
                | clear  H'3 H'2
                | clear  H'3 H'2 ]
             | clear H'3 H'2 ]
          | clear H'3 H'2 ]
    | clear H'2 ] 
  | idtac]; auto.
exists (Fnormalize radix b precision r); exists s.
cut (Fbounded b (Fnormalize radix b precision r));
 [ intros H5 | apply FnormalizeBounded; auto with arith ].
split; [ apply FnormalizeCanonic; auto with arith | idtac ].
repeat (split; auto).
unfold FtoRradix in |- *; rewrite <- H'19; unfold FtoRradix in |- *;
 apply FnormalizeCorrect; auto.
unfold FtoRradix in |- *; rewrite FnormalizeCorrect; auto with arith.
apply Zlt_le_weak.
apply
 RoundedModeErrorExpStrict with b radix precision (Closest b radix) (p * q)%R;
 auto with arith.
generalize ClosestCompatible; unfold CompatibleP in |- *; intros H6.
generalize
 (H6 b radix (FtoRradix p * FtoRradix q)%R (FtoRradix p * FtoRradix q)%R pq);
 intros H9; apply H9; auto.
rewrite FnormalizeCorrect; auto with real arith.
rewrite FnormalizeCorrect; auto with real arith.
rewrite H'21; rewrite H'19; auto.
apply Zle_trans with (Fexp r); auto.
apply FcanonicLeastExp with radix b precision; auto with arith.
rewrite FnormalizeCorrect; auto with real arith.
apply FnormalizeCanonic; auto with arith.
Qed.
 
Theorem errorBoundedMultClosest :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p * q) pq ->
 (- dExp b <= Fexp p + Fexp q)%Z ->
 (- dExp b <= Fexp (Fnormalize radix b precision pq) - precision)%Z ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fcanonic radix b r /\
       Fbounded b r /\
       Fbounded b s /\
       r = pq :>R /\
       s = (p * q - r)%R :>R /\ Fexp s = (Fexp r - precision)%Z :>Z)).
intros.
cut (RoundedModeP b radix (Closest b radix));
 [ intros G1 | apply ClosestRoundedModeP with precision; auto ].
case (Req_dec (p * q - pq) 0); intros U.
exists (Fnormalize radix b precision pq);
 exists (Fzero (Fexp (Fnormalize radix b precision pq) - precision)).
cut (Fbounded b pq);
 [ intros G2
 | apply RoundedModeBounded with radix (Closest b radix) (p * q)%R; auto ].
cut (Fcanonic radix b (Fnormalize radix b precision pq));
 [ intros G3 | apply FnormalizeCanonic; auto with arith ].
cut (Fbounded b (Fnormalize radix b precision pq));
 [ intros G4 | apply FnormalizeBounded; auto with arith ].
cut (Fnormalize radix b precision pq = pq :>R);
 [ intros G5
 | unfold FtoRradix in |- *; apply FnormalizeCorrect; auto with arith ].
repeat (split; auto).
rewrite G5; unfold FtoRradix in |- *; rewrite FzeroisReallyZero;
 auto with real.
lapply (errorBoundedMultClosest_aux p q pq); auto; intros H5.
lapply H5; auto; intros H6; clear H5.
lapply H6; auto; intros H5; clear H6.
lapply H5; auto; intros H6; clear H5.
lapply H6; auto; intros H5; clear H6.
elim H5; intros r H6; clear H5.
elim H6; intros s H5; clear H6.
elim H5; intros H7 H6; clear H5.
elim H6; intros H8 H9; clear H6.
elim H9; intros H6 H10; clear H9.
elim H10; intros H9 H11; clear H10.
elim H11; intros H10 H12; clear H11.
elim H12; intros H11 H13; clear H12.
elim H13; intros H12 H14; clear H13.
cut
 (ex
    (fun m : Z =>
     s = Float m (Fexp r - precision) :>R /\ (Zabs m <= pPred (vNum b))%Z)).
intros H13; elim H13; intros m H15; elim H15; intros H16 H17; clear H15 H13.
exists r; exists (Float m (Fexp r - precision)).
split; auto.
split; auto.
split.
2: repeat (split; auto).
2: rewrite <- H16; auto.
split; simpl in |- *.
generalize H17; unfold pPred in |- *; apply Zle_Zpred_inv.
replace r with (Fnormalize radix b precision pq); auto with zarith.
apply FcanonicUnique with radix b precision; auto with zarith.
apply FnormalizeCanonic; auto with zarith; elim H1; auto.
rewrite FnormalizeCorrect; auto with real zarith.
cut (radix <> 0%Z :>Z); [ intros V | auto with arith real zarith ].
cut (0 < radix)%Z; [ intros V2 | auto with arith real zarith ].
rewrite H10; unfold FtoRradix in |- *; rewrite <- Fmult_correct; auto.
rewrite <- Fminus_correct; fold FtoRradix in |- *; auto.
unfold Fmult in |- *; unfold Fminus in |- *; unfold Fopp in |- *;
 unfold Fplus in |- *; simpl in |- *.
unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *.
rewrite Zmin_le1; auto with zarith.
replace
 (Fnum p * Fnum q *
  Zpower_nat radix (Zabs_nat (Fexp p + Fexp q - (Fexp p + Fexp q))))%Z with
 (Fnum p * Fnum q)%Z.
2: replace (Fexp p + Fexp q - (Fexp p + Fexp q))%Z with 0%Z;
    auto with zarith arith; simpl in |- *.
2: auto with zarith.
exists
 ((Fnum p * Fnum q +
   - Fnum r * Zpower_nat radix (Zabs_nat (Fexp r - (Fexp p + Fexp q)))) *
  Zpower_nat radix (Zabs_nat (Fexp p + Fexp q + (precision - Fexp r))))%Z;
 split.
rewrite plus_IZR.
repeat rewrite Rmult_IZR.
rewrite plus_IZR.
repeat rewrite Rmult_IZR.
rewrite (Zpower_nat_powerRZ_absolu radix (Fexp r - (Fexp p + Fexp q))).
2: auto with zarith arith.
rewrite
 (Zpower_nat_powerRZ_absolu radix (Fexp p + Fexp q + (precision - Fexp r)))
 .
2: auto with zarith arith.
cut (radix <> 0%R :>R); [ intros W | auto with real arith zarith ].
unfold Zminus in |- *.
repeat rewrite powerRZ_add; try rewrite <- INR_IZR_INZ; auto.
apply
 trans_eq
  with
    ((Fnum p * Fnum q +
      (- Fnum r)%Z *
      (powerRZ radix (Fexp r) * powerRZ radix (- (Fexp p + Fexp q)))) *
     (powerRZ radix (Fexp p) * powerRZ radix (Fexp q)))%R.
ring; ring.
apply
 trans_eq
  with
    ((Fnum p * Fnum q +
      (- Fnum r)%Z *
      (powerRZ radix (Fexp r) * powerRZ radix (- (Fexp p + Fexp q)))) *
     (powerRZ radix (Fexp p) * powerRZ radix (Fexp q) *
      (powerRZ radix precision * powerRZ radix (- precision))) *
     (powerRZ radix (Fexp r) * powerRZ radix (- Fexp r)))%R.
2: ring; ring.
replace (powerRZ radix precision * powerRZ radix (- precision))%R with 1%R.
replace (powerRZ radix (Fexp r) * powerRZ radix (- Fexp r))%R with 1%R;
 try ring.
rewrite <- powerRZ_add; try rewrite <- INR_IZR_INZ; auto.
rewrite Zplus_opp_r; simpl in |- *; auto.
rewrite <- powerRZ_add; try rewrite <- INR_IZR_INZ; auto.
rewrite Zplus_opp_r; simpl in |- *; auto.
apply le_IZR; rewrite <- Faux.Rabsolu_Zabs.
rewrite Rmult_IZR; rewrite plus_IZR.
repeat rewrite Rmult_IZR.
rewrite
 (Zpower_nat_powerRZ_absolu radix (Fexp p + Fexp q + (precision - Fexp r)))
 .
2: auto with zarith arith.
rewrite (Zpower_nat_powerRZ_absolu radix (Fexp r - (Fexp p + Fexp q))).
2: auto with zarith arith.
rewrite powerRZ_add; try rewrite <- INR_IZR_INZ; auto with real arith.
replace
 ((Fnum p * Fnum q +
   (- Fnum r)%Z * powerRZ radix (Fexp r - (Fexp p + Fexp q))) *
  (powerRZ radix (Fexp p + Fexp q) * powerRZ radix (precision - Fexp r)))%R
 with
 ((Fnum p * Fnum q +
   (- Fnum r)%Z * powerRZ radix (Fexp r - (Fexp p + Fexp q))) *
  powerRZ radix (Fexp p + Fexp q) * powerRZ radix (precision - Fexp r))%R;
 [ idtac | ring; ring ].
rewrite Rabs_mult.
rewrite (Rabs_right (powerRZ radix (precision - Fexp r))).
2: apply Rle_ge; apply powerRZ_le; auto with real zarith.
apply Rmult_le_reg_l with (powerRZ radix (Fexp r - precision)).
apply powerRZ_lt; auto with real arith.
rewrite Rmult_comm; rewrite Rmult_assoc; rewrite <- powerRZ_add.
2: auto with zarith arith real.
replace (precision - Fexp r + (Fexp r - precision))%Z with 0%Z;
 [ simpl in |- * | ring ].
apply
 Rle_trans
  with
    (Rabs
       ((Fnum p * Fnum q +
         (- Fnum r)%Z * powerRZ radix (Fexp r - (Fexp p + Fexp q))) *
        powerRZ radix (Fexp p + Fexp q))); [ right; ring | idtac ].
replace
 ((Fnum p * Fnum q +
   (- Fnum r)%Z * powerRZ radix (Fexp r - (Fexp p + Fexp q))) *
  powerRZ radix (Fexp p + Fexp q))%R with (p * q - r)%R.
2: unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *;
    unfold Rminus in |- *.
2: unfold Zminus in |- *; repeat rewrite Ropp_Ropp_IZR.
2: repeat rewrite powerRZ_add; auto with real arith.
2: apply
    trans_eq
     with
       (Fnum p * Fnum q * (powerRZ radix (Fexp p) * powerRZ radix (Fexp q)) +
        - Fnum r *
        (powerRZ radix (Fexp r) *
         (powerRZ radix (- (Fexp p + Fexp q)) *
          (powerRZ radix (Fexp p) * powerRZ radix (Fexp q)))))%R;
    [ idtac | ring ].
2: replace
    (powerRZ radix (- (Fexp p + Fexp q)) *
     (powerRZ radix (Fexp p) * powerRZ radix (Fexp q)))%R with 1%R; 
    try ring.
2: repeat rewrite <- powerRZ_add; auto with real arith.
2: replace (- (Fexp p + Fexp q) + (Fexp p + Fexp q))%Z with 0%Z;
    simpl in |- *; simpl; ring.
apply Rle_trans with (powerRZ radix (Fexp r) * / 2%nat)%R.
rewrite <- H10;
 replace (powerRZ radix (Fexp r)) with (FtoRradix (Float 1%nat (Fexp r)));
 unfold FtoRradix in |- *;
 [ idtac | unfold FtoR in |- *; simpl in |- *; ring ].
apply ClosestErrorBound with b precision (p * q)%R; auto.
apply (ClosestCompatible b radix (p * q)%R (p * q)%R pq); auto.
unfold Zminus in |- *; rewrite powerRZ_add; auto with real arith.
rewrite Rmult_assoc; apply Rmult_le_compat_l.
apply powerRZ_le; auto with real arith.
unfold pPred, Zpred in |- *; rewrite pGivesBound.
rewrite plus_IZR; rewrite Zpower_nat_Z_powerRZ.
replace (powerRZ radix (- precision) * (powerRZ radix precision + (-1)%Z))%R
 with (1 + - powerRZ radix (- precision))%R.
apply Rle_trans with (1 + - powerRZ radix (- 1%nat))%R.
simpl in |- *.
replace (radix * 1)%R with (IZR radix); [ idtac | ring ].
replace (/ (1 + 1))%R with (1 + - / 2)%R.
apply Rplus_le_compat_l; apply Ropp_le_contravar.
apply Rle_Rinv; auto with real arith zarith.
replace 2%R with (1 + 1)%R; auto with real arith zarith.
cut ((1 + 1)%R <> 0%R :>R); [ intros | idtac ].
2: replace 2%R with (INR 2); auto with real arith zarith.
apply Rmult_eq_reg_l with (1 + 1)%R; auto.
rewrite Rmult_plus_distr_l.
simpl. rewrite (Rmult_comm (1 + 1) (- / (1 + 1))).
rewrite Ropp_mult_distr_l_reverse.
rewrite (Rmult_comm (/ (1 + 1)) (1 + 1)).
rewrite Rinv_r; auto with real; ring.
apply Rplus_le_compat_l; apply Ropp_le_contravar.
apply Rle_powerRZ; auto with real arith zarith.
rewrite Rmult_plus_distr_l.
rewrite <- powerRZ_add; auto with real arith.
replace (- precision + precision)%Z with 0%Z; simpl in |- *; ring.
Qed.
End FRoundP.
