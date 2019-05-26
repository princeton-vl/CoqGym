(****************************************************************************
                                                                             
          IEEE754  :  Fbound                                                   
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Fop.
Section Fbounded_Def.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Coercion Z_of_N: N >-> Z.
 
Record Fbound : Set := Bound {vNum : positive; dExp : N}.
 
Definition Fbounded (b : Fbound) (d : float) :=
  (Zabs (Fnum d) < Zpos (vNum b))%Z /\ (- dExp b <= Fexp d)%Z.
 
Theorem FboundedNum :
 forall (b : Fbound) (p : float),
 Fbounded b p -> (Zabs (Fnum p) < Zpos (vNum b))%Z.
intros b p H; case H; intros H1 H2; case H1; auto.
Qed.
 
Theorem FboundedExp :
 forall (b : Fbound) (p : float), Fbounded b p -> (- dExp b <= Fexp p)%Z.
intros b p H; case H; auto.
Qed.
Hint Resolve FboundedNum FboundedExp: float.
 
Theorem isBounded :
 forall (b : Fbound) (p : float), {Fbounded b p} + {~ Fbounded b p}.
intros b p; case (Z_le_gt_dec (Zpos (vNum b)) (Zabs (Fnum p)));
 intros H'.
right; red in |- *; intros H'3; Contradict H'; auto with float zarith.
case (Z_le_gt_dec (- dExp b) (Fexp p)); intros H'1.
left; repeat split; auto with zarith.
right; red in |- *; intros H'3; Contradict H'1; auto with float zarith.
Qed.
 
Theorem FzeroisZero : forall b : Fbound, Fzero (- dExp b) = 0%R :>R.
intros b; unfold FtoRradix, FtoR in |- *; simpl in |- *; auto with real.
Qed.
 
Theorem FboundedFzero : forall b : Fbound, Fbounded b (Fzero (- dExp b)).
intros b; repeat (split; simpl in |- *).
replace 0%Z with (- 0%nat)%Z; [ idtac | simpl in |- *; auto ].
apply Zeq_le; auto with arith.
Qed.
Hint Unfold Fbounded.
 
Theorem FboundedZeroSameExp :
 forall (b : Fbound) (p : float), Fbounded b p -> Fbounded b (Fzero (Fexp p)).
intros b p H'; (repeat split; simpl in |- *; auto with float zarith).
Qed.
 
Theorem FBoundedScale :
 forall (b : Fbound) (p : float) (n : nat),
 Fbounded b p -> Fbounded b (Float (Fnum p) (Fexp p + n)).
intros b p n H'; repeat split; simpl in |- *; auto with float.
apply Zle_trans with (Fexp p); auto with float.
pattern (Fexp p) at 1 in |- *;
 (replace (Fexp p) with (Fexp p + 0%nat)%Z; [ idtac | simpl in |- *; ring ]).
apply Zplus_le_compat_l.
apply inj_le; auto with arith.
Qed.
 
Theorem FvalScale :
 forall (b : Fbound) (p : float) (n : nat),
 Float (Fnum p) (Fexp p + n) = (powerRZ radix n * p)%R :>R.
intros b p n; unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_add; auto with real zarith.
ring.
Qed.
 
Theorem oppBounded :
 forall (b : Fbound) (x : float), Fbounded b x -> Fbounded b (Fopp x).
intros b x H'; repeat split; simpl in |- *; auto with float zarith.
replace (Zabs (- Fnum x)) with (Zabs (Fnum x)); auto with float.
case (Fnum x); simpl in |- *; auto.
Qed.
 
Theorem oppBoundedInv :
 forall (b : Fbound) (x : float), Fbounded b (Fopp x) -> Fbounded b x.
intros b x H'; rewrite <- (Fopp_Fopp x).
apply oppBounded; auto.
Qed.
 
Theorem FopRepAux :
 forall (b : Fbound) (z : Z) (p : R),
 ex (fun r : float => r = (- p)%R :>R /\ Fbounded b r /\ Fexp r = z) ->
 ex (fun r : float => r = p :>R /\ Fbounded b r /\ Fexp r = z).
intros b z p H'; elim H'; intros r E; elim E; intros H'0 H'1; elim H'1;
 intros H'2 H'3; clear H'1 E H'.
exists (Fopp r); split; auto.
rewrite <- (Ropp_involutive p).
rewrite <- H'0; auto.
unfold FtoRradix in |- *; apply Fopp_correct; auto.
split.
apply oppBounded; auto.
simpl in |- *; auto.
Qed.
 
Theorem absFBounded :
 forall (b : Fbound) (f : float), Fbounded b f -> Fbounded b (Fabs f).
intros b f H'; repeat split; simpl in |- *; auto with float.
replace (Zabs (Zabs (Fnum f))) with (Zabs (Fnum f)); auto with float.
case (Fnum f); auto.
Qed.
 
Theorem FboundedEqExpPos :
 forall (b : Fbound) (p q : float),
 Fbounded b p ->
 p = q :>R -> (Fexp p <= Fexp q)%R -> (0 <= q)%R -> Fbounded b q.
intros b p q H' H'0 H'1 H'2.
cut (0 <= Fnum p)%Z;
 [ intros Z1
 | apply (LeR0Fnum radix); auto with real arith; fold FtoRradix in |- *;
    rewrite H'0; auto ].
cut (0 <= Fnum q)%Z;
 [ intros Z2 | apply (LeR0Fnum radix); auto with real arith ].
split.
apply Zle_lt_trans with (Zabs (Fnum p)); [ idtac | auto with float ].
repeat rewrite Zabs_eq; auto.
apply Zle_trans with (Fnum (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q));
 auto.
unfold Fshift in |- *; simpl in |- *; auto.
pattern (Fnum q) at 1 in |- *; replace (Fnum q) with (Fnum q * 1)%Z;
 auto with zarith.
apply (Rle_Fexp_eq_Zle radix); auto with real zarith.
rewrite FshiftCorrect; auto with real zarith.
unfold Fshift in |- *; simpl in |- *; rewrite inj_abs; try ring.
apply Zle_Zminus_ZERO; apply le_IZR; auto with real arith.
apply Zle_trans with (Fexp p).
case H'; auto.
apply le_IZR; auto with real arith.
Qed.
 
Theorem FboundedEqExp :
 forall (b : Fbound) (p q : float),
 Fbounded b p -> p = q :>R -> (Fexp p <= Fexp q)%R -> Fbounded b q.
intros b p q H' H'0 H'1; split.
apply Zle_lt_trans with (Zabs (Fnum p)); [ idtac | auto with float ].
apply
 Zle_trans with (Zabs (Fnum (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q)));
 auto.
unfold Fshift in |- *; simpl in |- *; auto.
rewrite Zabs_Zmult.
pattern (Zabs (Fnum q)) at 1 in |- *;
 replace (Zabs (Fnum q)) with (Zabs (Fnum q) * 1%nat)%Z;
 [ apply Zle_Zmult_comp_l | auto with zarith ]; auto with zarith.
rewrite Zabs_eq; simpl in |- *; auto with zarith.
simpl in |- *; ring.
cut (Fexp p <= Fexp q)%Z; [ intros E2 | idtac ].
apply le_IZR; auto.
apply (Rle_monotony_contra_exp radix) with (z := Fexp p);
 auto with real arith.
pattern (Fexp p) at 2 in |- *;
 replace (Fexp p) with (Fexp (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q));
 auto.
rewrite <- (fun x => Rabs_pos_eq (powerRZ radix x)); auto with real zarith.
rewrite <- Faux.Rabsolu_Zabs.
rewrite <- Rabs_mult.
change
  (Rabs (FtoRradix (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q)) <=
   Zabs (Fnum p) * powerRZ radix (Fexp p))%R in |- *.
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto.
fold FtoRradix in |- *; rewrite <- H'0.
rewrite <- (Fabs_correct radix); auto with real zarith.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; [ ring | auto with zarith ].
cut (Fexp p <= Fexp q)%Z; [ intros E2 | apply le_IZR ]; auto.
apply Zle_trans with (Fexp p); [ idtac | apply le_IZR ]; auto with float.
Qed.
 
Theorem eqExpLess :
 forall (b : Fbound) (p q : float),
 Fbounded b p ->
 p = q :>R ->
 exists r : float, Fbounded b r /\ r = q :>R /\ (Fexp q <= Fexp r)%R.
intros b p q H' H'0.
case (Rle_or_lt (Fexp q) (Fexp p)); intros H'1.
exists p; repeat (split; auto).
exists q; split; [ idtac | split ]; auto with real.
apply FboundedEqExp with (p := p); auto.
apply Rlt_le; auto.
Qed.
 
Theorem FboundedShiftLess :
 forall (b : Fbound) (f : float) (n m : nat),
 m <= n -> Fbounded b (Fshift radix n f) -> Fbounded b (Fshift radix m f).
intros b f n m H' H'0; split; auto.
simpl in |- *; auto.
apply Zle_lt_trans with (Zabs (Fnum (Fshift radix n f))).
simpl in |- *; replace m with (m + 0); auto with arith.
replace n with (m + (n - m)); auto with arith.
repeat rewrite Zpower_nat_is_exp.
repeat rewrite Zabs_Zmult; auto.
apply Zle_Zmult_comp_l; auto with zarith.
apply Zle_Zmult_comp_l; auto with zarith.
repeat rewrite Zabs_eq; auto with zarith.
case H'0; auto.
apply Zle_trans with (Fexp (Fshift radix n f)); auto with float.
simpl in |- *; unfold Zminus in |- *; auto with zarith.
Qed.
 
Theorem eqExpMax :
 forall (b : Fbound) (p q : float),
 Fbounded b p ->
 Fbounded b q ->
 (Fabs p <= q)%R ->
 exists r : float, Fbounded b r /\ r = p :>R /\ (Fexp r <= Fexp q)%Z.
intros b p q H' H'0 H'1; case (Zle_or_lt (Fexp p) (Fexp q)); intros Rl0.
exists p; auto.
cut ((Fexp p - Zabs_nat (Fexp p - Fexp q))%Z = Fexp q);
 [ intros Eq1 | idtac ].
exists (Fshift radix (Zabs_nat (Fexp p - Fexp q)) p); split; split; auto.
apply Zle_lt_trans with (Fnum q); auto with float.
replace (Zabs (Fnum (Fshift radix (Zabs_nat (Fexp p - Fexp q)) p))) with
 (Fnum (Fabs (Fshift radix (Zabs_nat (Fexp p - Fexp q)) p))); 
 auto.
apply (Rle_Fexp_eq_Zle radix); auto with arith.
rewrite Fabs_correct; auto with arith; rewrite FshiftCorrect; auto with arith;
 rewrite <- (Fabs_correct radix); auto with float arith.
rewrite <- (Zabs_eq (Fnum q)); auto with float zarith.
apply (LeR0Fnum radix); auto.
apply Rle_trans with (2 := H'1); auto with real.
rewrite (Fabs_correct radix); auto with real zarith.
unfold Fshift in |- *; simpl in |- *; rewrite Eq1; auto with float.
unfold FtoRradix in |- *; apply FshiftCorrect; auto.
unfold Fshift in |- *; simpl in |- *.
rewrite Eq1; auto with zarith.
rewrite inj_abs; auto with zarith; ring.
Qed.
 
Theorem Zle_monotony_contra_abs_pow :
 forall x y z n : Z,
 (0 < z)%Z ->
 (Rabs (x * powerRZ z n) <= Rabs (y * powerRZ z n))%R -> (Zabs x <= Zabs y)%Z.
intros x y z n Hz O1.
apply le_IZR; auto.
apply Rmult_le_reg_l with (r := powerRZ z n); auto with real zarith.
repeat rewrite (Rmult_comm (powerRZ z n)); auto.
repeat rewrite <- Faux.Rabsolu_Zabs.
replace (powerRZ z n) with (Rabs (powerRZ z n)).
repeat rewrite <- Rabs_mult; auto.
apply Rabs_pos_eq; auto with real zarith.
Qed.
 
Theorem LessExpBound :
 forall (b : Fbound) (p q : float),
 Fbounded b p ->
 Fbounded b q ->
 (Fexp q <= Fexp p)%Z ->
 (0 <= p)%R ->
 (p <= q)%R ->
 exists m : Z,
   Float m (Fexp q) = p :>R /\ Fbounded b (Float m (Fexp q)).
intros b p q H' H'0 H'1 H'2 H'3;
 exists (Fnum p * Zpower_nat radix (Zabs_nat (Fexp p - Fexp q)))%Z.
cut
 (Float (Fnum p * Zpower_nat radix (Zabs_nat (Fexp p - Fexp q))) (Fexp q) = p
  :>R); [ intros Eq1 | idtac ].
split; auto.
repeat split; simpl in |- *; auto with float.
apply Zle_lt_trans with (Zabs (Fnum q)); auto with float.
apply Zle_monotony_contra_abs_pow with (z := radix) (n := Fexp q);
 auto with real arith.
unfold FtoRradix, FtoR in Eq1; simpl in Eq1; rewrite Eq1; auto with real.
change (Rabs p <= Rabs q)%R in |- *.
repeat rewrite Rabs_pos_eq; auto with real.
apply Rle_trans with (1 := H'2); auto.
pattern (Fexp q) at 2 in |- *;
 replace (Fexp q) with (Fexp p - Zabs_nat (Fexp p - Fexp q))%Z.
change (Fshift radix (Zabs_nat (Fexp p - Fexp q)) p = p :>R) in |- *.
unfold FtoRradix in |- *; apply FshiftCorrect; auto.
rewrite inj_abs; auto with zarith; ring.
Qed.
 
Theorem maxFbounded :
 forall (b : Fbound) (z : Z),
 (- dExp b <= z)%Z -> Fbounded b (Float (Zpred (Zpos (vNum b))) z).
intros b z H; split; auto.
change (Zabs (Zpred (Zpos (vNum b))) < Zpos (vNum b))%Z in |- *.
rewrite Zabs_eq; auto with zarith.
Qed.
 
Theorem maxMax :
 forall (b : Fbound) (p : float) (z : Z),
 Fbounded b p ->
 (Fexp p <= z)%Z -> (Fabs p < Float (Zpos (vNum b)) z)%R.
intros b p z H' H'0; unfold FtoRradix in |- *;
 rewrite <-
  (FshiftCorrect _ radixMoreThanOne (Zabs_nat (z - Fexp p))
     (Float (Zpos (vNum b)) z)); unfold Fshift in |- *.
change
  (FtoR radix (Fabs p) <
   FtoR radix
     (Float (Zpos (vNum b) * Zpower_nat radix (Zabs_nat (z - Fexp p)))
        (z - Zabs_nat (z - Fexp p))))%R in |- *.
replace (z - Zabs_nat (z - Fexp p))%Z with (Fexp p).
unfold Fabs, FtoR in |- *.
change
  (Zabs (Fnum p) * powerRZ radix (Fexp p) <
   (Zpos (vNum b) * Zpower_nat radix (Zabs_nat (z - Fexp p)))%Z *
   powerRZ radix (Fexp p))%R in |- *.
apply Rmult_lt_compat_r; auto with real zarith.
apply Rlt_le_trans with (IZR (Zpos (vNum b)));
 auto with real float zarith.
pattern (Zpos (vNum b)) at 1 in |- *;
 replace (Zpos (vNum b)) with (Zpos (vNum b) * 1)%Z;
 auto with real float zarith; ring.
rewrite inj_abs; auto with zarith; ring.
Qed.
End Fbounded_Def.
Hint Resolve FboundedFzero oppBounded absFBounded maxFbounded FboundedNum
  FboundedExp: float.