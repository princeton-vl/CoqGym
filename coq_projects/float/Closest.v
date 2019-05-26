(****************************************************************************
                                                                             
          IEEE754  :  Closest                                                   
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  Properties about the closest rounding mode *)
Require Export Fround.
Section Fclosest.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Definition Closest (r : R) (p : float) :=
  Fbounded b p /\
  (forall f : float, Fbounded b f -> (Rabs (p - r) <= Rabs (f - r))%R).
 
Theorem ClosestTotal : TotalP Closest.
red in |- *; intros r.
case MinEx with (r := r) (3 := pGivesBound); auto with arith.
intros min H'.
case MaxEx with (r := r) (3 := pGivesBound); auto with arith.
intros max H'0.
cut (min <= r)%R; [ intros Rl1 | apply isMin_inv1 with (1 := H') ].
cut (r <= max)%R; [ intros Rl2 | apply isMax_inv1 with (1 := H'0) ].
case (Rle_or_lt (Rabs (min - r)) (Rabs (max - r))); intros H'1.
exists min; split.
case H'; auto.
intros f H'2.
case (Rle_or_lt f r); intros H'3.
repeat rewrite Faux.Rabsolu_left1.
apply Ropp_le_contravar; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
elim H'; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rle_trans with (1 := H'1).
repeat rewrite Rabs_right.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
elim H'0; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rlt_le; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r.
apply Rlt_le; auto.
repeat rewrite Rplus_minus; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
exists max; split.
case H'0; auto.
intros f H'2.
case (Rle_or_lt f r); intros H'3.
apply Rle_trans with (1 := Rlt_le _ _ H'1).
repeat rewrite Faux.Rabsolu_left1.
apply Ropp_le_contravar; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
elim H'; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
repeat rewrite Rabs_right; auto with real.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
elim H'0; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rlt_le; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rlt_le; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
Qed.
 
Theorem ClosestCompatible : CompatibleP b radix Closest.
red in |- *; simpl in |- *.
intros r1 r2 p q H'; case H'.
intros H'0 H'1 H'2 H'3 H'4.
split; auto.
intros f H'5.
unfold FtoRradix in |- *; rewrite <- H'3; rewrite <- H'2; auto.
Qed.
 
Theorem ClosestMin :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max -> (2%nat * r <= min + max)%R -> Closest r min.
intros r min max H' H'0 H'1; split.
case H'; auto.
intros f H'2.
case (Rle_or_lt f r); intros H'3.
repeat rewrite Faux.Rabsolu_left1.
apply Ropp_le_contravar.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
case H'; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMin_inv1 with (1 := H'); auto.
rewrite (Faux.Rabsolu_left1 (min - r)).
rewrite (Rabs_right (f - r)).
apply Rle_trans with (max - r)%R.
cut (forall x y : R, (- y + x)%R = (- (y - x))%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
cut (forall x y : R, (- (x - y))%R = (y - x)%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0
 | intros; unfold Rminus in |- *; ring ].
apply Rplus_le_reg_l with (r := FtoR radix min).
repeat rewrite Rplus_minus; auto.
apply Rplus_le_reg_l with (r := r).
replace (r + (FtoR radix min + (max - r)))%R with (min + max)%R.
replace (r + r)%R with (2%nat * r)%R; auto.
simpl in |- *; ring.
simpl in |- *; fold FtoRradix; ring.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
case H'0; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rlt_le; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rlt_le; auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMin_inv1 with (1 := H'); auto.
Qed.
 
Theorem ClosestMax :
 forall (r : R) (min max : float),
 isMin b radix r min ->
 isMax b radix r max -> (min + max <= 2%nat * r)%R -> Closest r max.
intros r min max H' H'0 H'1; split.
case H'0; auto.
intros f H'2.
case (Rle_or_lt f r); intros H'3.
rewrite (Rabs_right (max - r)).
rewrite (Faux.Rabsolu_left1 (f - r)).
apply Rle_trans with (r - min)%R.
apply Rplus_le_reg_l with (r := FtoRradix min).
repeat rewrite Rplus_minus; auto.
apply Rplus_le_reg_l with (r := r).
replace (r + (min + (max - r)))%R with (min + max)%R.
replace (r + r)%R with (2%nat * r)%R; auto.
simpl in |- *; ring.
simpl in |- *; ring.
replace (r - min)%R with (- (min - r))%R.
apply Ropp_le_contravar.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
case H'; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
simpl in |- *; ring.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMax_inv1 with (1 := H'0); auto.
repeat rewrite Rabs_right.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
case H'0; auto.
intros H'4 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
apply Rlt_le; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rlt_le; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMax_inv1 with (1 := H'0); auto.
Qed.
 
Theorem ClosestMinOrMax : MinOrMaxP b radix Closest.
red in |- *.
intros r p H'.
case (Rle_or_lt p r); intros H'1.
left; split; auto.
case H'; auto.
split; auto.
intros f H'0 H'2.
apply Rplus_le_reg_l with (r := (- r)%R).
cut (forall x y : R, (- y + x)%R = (- (y - x))%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
apply Ropp_le_contravar.
rewrite <- (Rabs_right (r - FtoR radix p)).
rewrite <- (Rabs_right (r - FtoR radix f)).
cut (forall x y : R, Rabs (x - y) = Rabs (y - x));
 [ intros Eq0; repeat rewrite (Eq0 r); clear Eq0
 | intros x y; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr ];
 auto.
elim H'; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix f).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix p).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
right; split; auto.
case H'; auto.
split; auto.
apply Rlt_le; auto.
intros f H'0 H'2.
apply Rplus_le_reg_l with (r := (- r)%R).
cut (forall x y : R, (- y + x)%R = (- (y - x))%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
rewrite <- (Faux.Rabsolu_left1 (r - FtoR radix p)).
rewrite <- (Faux.Rabsolu_left1 (r - FtoR radix f)).
cut (forall x y : R, Rabs (x - y) = Rabs (y - x));
 [ intros Eq0; repeat rewrite (Eq0 r); clear Eq0
 | intros x y; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr ];
 auto.
elim H'; auto.
apply Rplus_le_reg_l with (r := FtoR radix f).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rplus_le_reg_l with (r := FtoR radix p).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rlt_le; auto.
Qed.
 
Theorem ClosestMinEq :
 forall (r : R) (min max p : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (2%nat * r < min + max)%R -> Closest r p -> p = min :>R.
intros r min max p H' H'0 H'1 H'2.
case (ClosestMinOrMax r p); auto; intros H'3.
unfold FtoRradix in |- *; apply MinEq with (1 := H'3); auto.
absurd (Rabs (max - r) <= Rabs (min - r))%R.
apply Rgt_not_le.
rewrite (Faux.Rabsolu_left1 (min - r)).
rewrite Rabs_right.
replace (- (min - r))%R with (r - min)%R; [ idtac | ring ].
red in |- *; apply Rplus_lt_reg_l with (r := FtoRradix min).
repeat rewrite Rplus_minus; auto.
apply Rplus_lt_reg_l with (r := r).
replace (r + r)%R with (2%nat * r)%R; [ idtac | simpl in |- *; ring ].
replace (r + (min + (max - r)))%R with (min + max)%R; [ idtac | ring ]; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMax_inv1 with (1 := H'0); auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMin_inv1 with (1 := H'); auto.
cut (Closest r max).
intros H'4; case H'4.
intros H'5 H'6; apply H'6; auto.
case H'; auto.
apply ClosestCompatible with (1 := H'2); auto.
apply MaxEq with (1 := H'3); auto.
case H'0; auto.
Qed.
 
Theorem ClosestMaxEq :
 forall (r : R) (min max p : float),
 isMin b radix r min ->
 isMax b radix r max ->
 (min + max < 2%nat * r)%R -> Closest r p -> p = max :>R.
intros r min max p H' H'0 H'1 H'2.
case (ClosestMinOrMax r p); auto; intros H'3.
2: unfold FtoRradix in |- *; apply MaxEq with (1 := H'3); auto.
absurd (Rabs (min - r) <= Rabs (max - r))%R.
apply Rgt_not_le.
rewrite (Faux.Rabsolu_left1 (min - r)).
rewrite Rabs_right.
replace (- (min - r))%R with (r - min)%R; [ idtac | ring ].
red in |- *; apply Rplus_lt_reg_l with (r := FtoRradix min).
repeat rewrite Rplus_minus; auto.
apply Rplus_lt_reg_l with (r := r).
replace (r + r)%R with (2%nat * r)%R; [ idtac | simpl in |- *; ring ].
replace (r + (min + (max - r)))%R with (min + max)%R; [ idtac | ring ]; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMax_inv1 with (1 := H'0); auto.
apply Rplus_le_reg_l with (r := r).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply isMin_inv1 with (1 := H'); auto.
cut (Closest r min).
intros H'4; case H'4.
intros H'5 H'6; apply H'6; auto.
case H'0; auto.
apply ClosestCompatible with (1 := H'2); auto.
apply MinEq with (1 := H'3); auto.
case H'; auto.
Qed.
 
Theorem ClosestMonotone : MonotoneP radix Closest.
red in |- *; simpl in |- *.
intros p q p' q' H' H'0 H'1.
change (p' <= q')%R in |- *.
case (Rle_or_lt p p'); intros Rl0.
case (Rle_or_lt p q'); intros Rl1.
apply Rplus_le_reg_l with (r := (- p)%R).
cut (forall x y : R, (- y + x)%R = (- (y - x))%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
rewrite <- (Faux.Rabsolu_left1 (p - p')).
rewrite <- (Faux.Rabsolu_left1 (p - q')).
cut (forall x y : R, Rabs (x - y) = Rabs (y - x));
 [ intros Eq0; repeat rewrite (Eq0 p); clear Eq0
 | intros x y; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr ];
 auto.
elim H'0; auto.
intros H'2 H'3; apply H'3; auto.
case H'1; auto.
apply Rplus_le_reg_l with (r := FtoR radix q').
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rplus_le_reg_l with (r := FtoR radix p').
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
case (Rle_or_lt p' q); intros Rl2.
apply Rplus_le_reg_l with (r := (- q)%R).
cut (forall x y : R, (- y + x)%R = (- (y - x))%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
rewrite <- (Rabs_right (q - p')).
2: apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix p').
2: repeat rewrite Rplus_minus; auto.
2: rewrite Rplus_0_r; auto.
rewrite <- (Rabs_right (q - q')).
2: apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix q').
2: repeat rewrite Rplus_minus; auto.
2: rewrite Rplus_0_r; auto.
2: apply Rle_trans with (1 := Rlt_le _ _ Rl1); apply Rlt_le; auto.
cut (forall x y : R, Rabs (x - y) = Rabs (y - x));
 [ intros Eq0; repeat rewrite (Eq0 q); clear Eq0
 | intros x y; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr ];
 auto.
apply Ropp_le_contravar.
elim H'1; auto.
intros H'2 H'3; apply H'3; auto.
case H'0; auto.
case (Rle_or_lt (p - q') (p' - q)); intros Rl3.
absurd (Rabs (p' - p) <= Rabs (q' - p))%R.
apply Rgt_not_le.
rewrite (Faux.Rabsolu_left1 (q' - p)).
2: apply Rplus_le_reg_l with (r := p).
2: repeat rewrite Rplus_minus; auto.
2: rewrite Rplus_0_r; apply Rlt_le; auto.
rewrite (Rabs_right (p' - p)).
2: apply Rle_ge; apply Rplus_le_reg_l with (r := p).
2: rewrite Rplus_0_r; auto.
cut (forall x y : R, (- (y - x))%R = (x - y)%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
red in |- *; apply Rle_lt_trans with (1 := Rl3).
replace (p' - p)%R with (p' - q + (q - p))%R.
pattern (p' - q)%R at 1 in |- *; replace (p' - q)%R with (p' - q + 0)%R.
apply Rplus_lt_compat_l; auto.
apply Rplus_lt_reg_l with (r := p).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
rewrite Rplus_0_r; auto.
ring.
replace (p + (p' - p))%R with (FtoRradix p'); auto; ring.
case H'0; intros H'2 H'3; apply H'3; auto.
case H'1; auto.
absurd (Rabs (q' - q) <= Rabs (p' - q))%R.
apply Rgt_not_le.
rewrite (Faux.Rabsolu_left1 (q' - q)).
2: apply Rplus_le_reg_l with (r := q).
2: repeat rewrite Rplus_minus; auto.
2: rewrite Rplus_0_r; apply Rlt_le; auto.
2: apply Rlt_trans with (1 := Rl1); auto.
rewrite (Rabs_right (p' - q)).
2: apply Rle_ge; apply Rplus_le_reg_l with (r := q).
2: rewrite Rplus_0_r; apply Rlt_le; auto.
cut (forall x y : R, (- (y - x))%R = (x - y)%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
red in |- *; apply Rlt_trans with (1 := Rl3).
replace (q - q')%R with (p - q' + (q - p))%R.
pattern (p - q')%R at 1 in |- *; replace (p - q')%R with (p - q' + 0)%R.
apply Rplus_lt_compat_l; auto.
apply Rplus_lt_reg_l with (r := p).
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
rewrite Rplus_0_r; auto.
ring.
replace (q + (p' - q))%R with (FtoRradix p'); auto; ring.
case H'1; intros H'2 H'3; apply H'3; auto.
case H'0; auto.
case (Rle_or_lt p q'); intros Rl1.
apply Rle_trans with p; auto.
apply Rlt_le; auto.
apply Rplus_le_reg_l with (r := (- q)%R).
cut (forall x y : R, (- y + x)%R = (- (y - x))%R);
 [ intros Eq0; repeat rewrite Eq0; clear Eq0 | intros; ring ].
rewrite <- (Rabs_right (q - p')).
rewrite <- (Rabs_right (q - q')).
apply Ropp_le_contravar.
cut (forall x y : R, Rabs (x - y) = Rabs (y - x));
 [ intros Eq0; repeat rewrite (Eq0 q); clear Eq0
 | intros x y; rewrite <- (Rabs_Ropp (x - y)); rewrite Ropp_minus_distr ];
 auto.
elim H'1; auto.
intros H'2 H'3; apply H'3; auto.
case H'0; auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix q').
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rlt_le; apply Rlt_trans with (1 := Rl1); auto.
apply Rle_ge; apply Rplus_le_reg_l with (r := FtoR radix p').
repeat rewrite Rplus_minus; auto.
rewrite Rplus_0_r; auto.
apply Rlt_le; apply Rlt_trans with (1 := Rl0); auto.
Qed.
 
Theorem ClosestRoundedModeP : RoundedModeP b radix Closest.
split; try exact ClosestTotal.
split; try exact ClosestCompatible.
split; try exact ClosestMinOrMax.
try exact ClosestMonotone.
Qed.
 
Definition EvenClosest (r : R) (p : float) :=
  Closest r p /\
  (FNeven b radix precision p \/ (forall q : float, Closest r q -> q = p :>R)).
 
Theorem EvenClosestTotal : TotalP EvenClosest.
red in |- *; intros r.
case MinEx with (r := r) (3 := pGivesBound); auto with arith.
intros min H'.
case MaxEx with (r := r) (3 := pGivesBound); auto with arith.
intros max H'0.
cut (min <= r)%R; [ intros Rl1 | apply isMin_inv1 with (1 := H'); auto ].
cut (r <= max)%R; [ intros Rl2 | apply isMax_inv1 with (1 := H'0) ].
case (Rle_or_lt (r - min) (max - r)); intros H'1.
case H'1; intros H'2; auto.
exists min; split.
apply ClosestMin with (max := max); auto.
replace (2%nat * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
apply Rminus_le; auto.
replace (r + r - (min + max))%R with (r - min - (max - r))%R;
 [ idtac | simpl in |- *; ring ].
apply Rle_minus; auto.
right; intros q H'3.
apply ClosestMinEq with (r := r) (max := max); auto.
replace (2%nat * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
apply Rminus_lt; auto.
replace (r + r - (min + max))%R with (r - min - (max - r))%R;
 [ idtac | simpl in |- *; ring ].
apply Rlt_minus; auto.
case (FNevenOrFNodd b radix precision min); intros Ev0.
exists min; split; auto.
apply ClosestMin with (max := max); auto.
replace (2%nat * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
apply Rminus_le; auto.
replace (r + r - (min + max))%R with (r - min - (max - r))%R;
 [ idtac | simpl in |- *; ring ].
apply Rle_minus; auto.
exists max; split; auto.
apply ClosestMax with (min := min); auto.
replace (2%nat * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
apply Rminus_le; auto.
replace (min + max - (r + r))%R with (max - r - (r - min))%R;
 [ idtac | simpl in |- *; ring ].
apply Rle_minus; auto.
rewrite H'2; auto with real.
case (Req_dec min max); intros H'5.
right; intros q H'3.
case (ClosestMinOrMax _ _ H'3); intros isM0.
rewrite <- H'5.
apply MinEq with (1 := isM0); auto.
apply MaxEq with (1 := isM0); auto.
left.
apply FNevenEq with (f1 := FNSucc b radix precision min); auto.
apply FcanonicBound with (radix := radix).
apply FNSuccCanonic; auto with arith.
case H'; auto.
case H'0; auto.
apply MaxEq with (b := b) (r := r); auto.
apply MinMax; auto with arith.
Contradict H'5; auto.
fold FtoRradix in H'5; rewrite H'5 in H'2.
replace (FtoRradix max) with (min + (max - min))%R;
 [ rewrite <- H'2 | idtac ]; ring.
apply FNoddSuc; auto.
case H'; auto.
exists max; split; auto.
apply ClosestMax with (min := min); auto.
replace (2%nat * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
apply Rminus_le; auto.
replace (min + max - (r + r))%R with (max - r - (r - min))%R;
 [ idtac | simpl in |- *; ring ].
apply Rle_minus; auto with real.
right; intros q H'2.
apply ClosestMaxEq with (r := r) (min := min); auto.
replace (2%nat * r)%R with (r + r)%R; [ idtac | simpl in |- *; ring ].
apply Rminus_lt; auto.
replace (min + max - (r + r))%R with (max - r - (r - min))%R;
 [ idtac | simpl in |- *; ring ].
apply Rlt_minus; auto.
Qed.
 
Theorem EvenClosestCompatible : CompatibleP b radix EvenClosest.
red in |- *; simpl in |- *.
intros r1 r2 p q H' H'0 H'1 H'2; red in |- *.
inversion H'.
split.
apply (ClosestCompatible r1 r2 p q); auto.
case H0; intros H1.
left.
apply FNevenEq with (f1 := p); auto.
case H; auto.
right; intros q0 H'3.
unfold FtoRradix in |- *; rewrite <- H'1; auto.
apply H1; auto.
apply (ClosestCompatible r2 r1 q0 q0); auto.
case H'3; auto.
Qed.
 
Theorem EvenClosestMinOrMax : MinOrMaxP b radix EvenClosest.
red in |- *; intros r p H'; case (ClosestMinOrMax r p); auto.
case H'; auto.
Qed.
 
Theorem EvenClosestMonotone : MonotoneP radix EvenClosest.
red in |- *; simpl in |- *; intros p q p' q' H' H'0 H'1.
apply (ClosestMonotone p q); auto; case H'0; case H'1; auto.
Qed.
 
Theorem EvenClosestRoundedModeP : RoundedModeP b radix EvenClosest.
red in |- *; split.
exact EvenClosestTotal.
split.
exact EvenClosestCompatible.
split.
exact EvenClosestMinOrMax.
exact EvenClosestMonotone.
Qed.
 
Theorem EvenClosestUniqueP : UniqueP radix EvenClosest.
red in |- *; simpl in |- *.
intros r p q H' H'0.
inversion H'; inversion H'0; case H0; case H2; auto.
intros H'1 H'2; case (EvenClosestMinOrMax r p);
 case (EvenClosestMinOrMax r q); auto.
intros H'3 H'4; apply (MinUniqueP b radix r); auto.
intros H'3 H'4; case (Req_dec p q); auto; intros H'5.
Contradict H'1; auto.
apply FnOddNEven; auto.
apply FNoddEq with (f1 := FNSucc b radix precision p); auto.
apply FcanonicBound with (radix := radix); auto.
apply FNSuccCanonic; auto with arith.
case H'4; auto.
case H'3; auto.
apply (MaxUniqueP b radix r); auto.
apply MinMax; auto with arith.
Contradict H'5; auto.
apply
 (RoundedProjector b radix _
    (MaxRoundedModeP _ _ _ radixMoreThanOne precisionGreaterThanOne
       pGivesBound)); auto.
case H'4; auto.
rewrite <- H'5; auto.
apply FNevenSuc; auto.
case H'4; auto.
intros H'3 H'4; case (Req_dec p q); auto; intros H'5.
Contradict H'2; auto.
apply FnOddNEven; auto.
apply FNoddEq with (f1 := FNSucc b radix precision q); auto.
apply FcanonicBound with (radix := radix); auto.
apply FNSuccCanonic; auto with arith.
case H'3; auto.
case H'4; auto.
apply (MaxUniqueP b radix r); auto.
apply MinMax; auto with arith.
Contradict H'5; auto.
apply sym_eq;
 apply
  (RoundedProjector b radix _
     (MaxRoundedModeP _ _ _ radixMoreThanOne precisionGreaterThanOne
        pGivesBound)); auto.
case H'3; auto.
rewrite <- H'5; auto.
apply FNevenSuc; auto.
case H'3; auto.
intros H'3 H'4; apply (MaxUniqueP b radix r); auto.
intros H'1 H'2; apply sym_eq; auto.
Qed.
 
Theorem ClosestSymmetric : SymmetricP Closest.
red in |- *; intros r p H'; case H'; clear H'.
intros H' H'0; split.
apply oppBounded; auto.
intros f H'1.
replace (Rabs (Fopp p - - r)) with (Rabs (p - r)).
replace (Rabs (f - - r)) with (Rabs (Fopp f - r)).
apply H'0; auto.
apply oppBounded; auto.
unfold FtoRradix in |- *; rewrite Fopp_correct.
pattern r at 1 in |- *; replace r with (- - r)%R; [ idtac | ring ].
replace (- FtoR radix f - - - r)%R with (- (FtoR radix f - - r))%R;
 [ idtac | ring ].
apply Rabs_Ropp; auto.
unfold FtoRradix in |- *; rewrite Fopp_correct.
replace (- FtoR radix p - - r)%R with (- (FtoR radix p - r))%R;
 [ idtac | ring ].
apply sym_eq; apply Rabs_Ropp.
Qed.
 
Theorem EvenClosestSymmetric : SymmetricP EvenClosest.
red in |- *; intros r p H'; case H'; clear H'.
intros H' H'0; case H'0; clear H'0; intros H'0.
split; auto.
apply (ClosestSymmetric r p); auto.
left.
apply FNevenFop; auto.
split; auto.
apply (ClosestSymmetric r p); auto.
right.
intros q H'1.
cut (Fopp q = p :>R).
intros H'2; unfold FtoRradix in |- *; rewrite Fopp_correct.
unfold FtoRradix in H'2; rewrite <- H'2.
rewrite Fopp_correct; ring.
apply H'0; auto.
replace r with (- - r)%R; [ idtac | ring ].
apply (ClosestSymmetric (- r)%R q); auto.
Qed.
End Fclosest.
Hint Resolve ClosestTotal ClosestCompatible ClosestMin ClosestMax
  ClosestMinOrMax ClosestMonotone ClosestRoundedModeP EvenClosestTotal
  EvenClosestCompatible EvenClosestMinOrMax EvenClosestMonotone
  EvenClosestRoundedModeP FnOddNEven EvenClosestUniqueP ClosestSymmetric
  EvenClosestSymmetric: float.