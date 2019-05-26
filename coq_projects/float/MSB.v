(****************************************************************************
                                                                             
          IEEE754  :  MSB                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Fprop.
Require Export Zdivides.
Require Export Fnorm.
Section mf.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Fixpoint maxDiv (v : Z) (p : nat) {struct p} : nat :=
  match p with
  | O => 0
  | S p' =>
      match ZdividesP v (Zpower_nat radix p) with
      | left _ => p
      | right _ => maxDiv v p'
      end
  end.
 
Theorem maxDivLess : forall (v : Z) (p : nat), maxDiv v p <= p.
intros v p; elim p; simpl in |- *; auto.
intros n H'; case (ZdividesP v (radix * Zpower_nat radix n)); auto.
Qed.
 
Theorem maxDivLt :
 forall (v : Z) (p : nat),
 ~ Zdivides v (Zpower_nat radix p) -> maxDiv v p < p.
intros v p; case p; simpl in |- *; auto.
intros H'; case H'.
apply Zdivides1.
intros n H'; case (ZdividesP v (radix * Zpower_nat radix n)); auto.
intros H'0; case H'; auto.
intros H'0; generalize (maxDivLess v n); auto with arith.
Qed.
 
Theorem maxDivCorrect :
 forall (v : Z) (p : nat), Zdivides v (Zpower_nat radix (maxDiv v p)).
intros v p; elim p.
unfold maxDiv in |- *; rewrite Zpower_nat_O; auto.
apply Zdivides1.
simpl in |- *.
intros n H'; case (ZdividesP v (radix * Zpower_nat radix n)); simpl in |- *;
 auto with zarith.
Qed.
 
Theorem maxDivSimplAux :
 forall (v : Z) (p q : nat),
 p = maxDiv v (S (q + p)) -> p = maxDiv v (S p).
intros v p q; elim q.
simpl in |- *; case (ZdividesP v (radix * Zpower_nat radix p)); auto.
intros n H' H'0.
apply H'; auto; clear H'.
simpl in H'0; generalize H'0; clear H'0.
case (ZdividesP v (radix * (radix * Zpower_nat radix (n + p)))).
2: simpl in |- *; auto.
intros H' H'0; Contradict H'0; auto with zarith.
Qed.
 
Theorem maxDivSimpl :
 forall (v : Z) (p q : nat),
 p < q -> p = maxDiv v q -> p = maxDiv v (S p).
intros v p q H' H'0.
apply maxDivSimplAux with (q := q - S p); auto.
replace (S (q - S p + p)) with q; auto with zarith.
Qed.
 
Theorem maxDivSimplInvAux :
 forall (v : Z) (p q : nat),
 p = maxDiv v (S p) -> p = maxDiv v (S (q + p)).
intros v p q H'; elim q.
simpl in |- *; auto.
intros n; simpl in |- *.
case (ZdividesP v (radix * Zpower_nat radix (n + p))); auto.
case (ZdividesP v (radix * (radix * Zpower_nat radix (n + p)))); auto.
intros H'0 H'1 H'2; Contradict H'2; auto with zarith.
case (ZdividesP v (radix * (radix * Zpower_nat radix (n + p)))); auto.
intros H'0 H'1 H'2; case H'1.
case H'0; intros z1 Hz1; exists (radix * z1)%Z;rewrite Hz1.
unfold Zpower_nat; simpl; ring.
Qed.
 
Theorem maxDivSimplInv :
 forall (v : Z) (p q : nat),
 p < q -> p = maxDiv v (S p) -> p = maxDiv v q.
intros v p q H' H'0.
replace q with (S (q - S p + p)); auto with zarith.
apply maxDivSimplInvAux; auto.
Qed.
 
Theorem maxDivUnique :
 forall (v : Z) (p : nat),
 p = maxDiv v (S p) ->
 Zdivides v (Zpower_nat radix p) /\ ~ Zdivides v (Zpower_nat radix (S p)).
intros v p H'; split.
rewrite H'.
apply maxDivCorrect; auto.
red in |- *; intros H'0; generalize H'; clear H'.
simpl in |- *.
case (ZdividesP v (radix * Zpower_nat radix p)); simpl in |- *; auto.
intros H' H'1; Contradict H'1; auto with zarith.
Qed.
 
Theorem maxDivUniqueDigit :
 forall v : Z,
 v <> 0 ->
 Zdivides v (Zpower_nat radix (maxDiv v (digit radix v))) /\
 ~ Zdivides v (Zpower_nat radix (S (maxDiv v (digit radix v)))).
intros v H'.
apply maxDivUnique; auto.
apply maxDivSimpl with (q := digit radix v); auto.
apply maxDivLt; auto.
apply NotDividesDigit; auto.
Qed.
 
Theorem maxDivUniqueInverse :
 forall (v : Z) (p : nat),
 Zdivides v (Zpower_nat radix p) ->
 ~ Zdivides v (Zpower_nat radix (S p)) -> p = maxDiv v (S p).
intros v p H' H'0; simpl in |- *.
case (ZdividesP v (radix * Zpower_nat radix p)); auto.
intros H'1; case H'0; simpl in |- *; auto.
intros H'1.
generalize H'; case p; simpl in |- *; auto.
intros n H'2; case (ZdividesP v (radix * Zpower_nat radix n)); auto.
intros H'3; case H'3; auto.
Qed.
 
Theorem maxDivUniqueInverseDigit :
 forall (v : Z) (p : nat),
 v <> 0 ->
 Zdivides v (Zpower_nat radix p) ->
 ~ Zdivides v (Zpower_nat radix (S p)) -> p = maxDiv v (digit radix v).
intros v p H' H'0 H'1.
apply maxDivSimplInv; auto.
2: apply maxDivUniqueInverse; auto.
apply Zpower_nat_anti_monotone_lt with (n := radix); auto.
apply Zle_lt_trans with (m := Zabs v); auto.
rewrite <- (fun x => Zabs_eq (Zpower_nat radix x)); auto with zarith;
 apply ZDividesLe; auto.
apply digitMore; auto.
Qed.
 
Theorem maxDivPlus :
 forall (v : Z) (n : nat),
 v <> 0 ->
 maxDiv (v * Zpower_nat radix n) (digit radix v + n) =
 maxDiv v (digit radix v) + n.
intros v n H.
replace (digit radix v + n) with (digit radix (v * Zpower_nat radix n)); auto.
apply sym_equal.
apply maxDivUniqueInverseDigit; auto.
red in |- *; intros Z1; case (Zmult_integral _ _ Z1); intros Z2.
case H; auto.
absurd (0 < Zpower_nat radix n)%Z; auto with zarith.
rewrite Zpower_nat_is_exp.
repeat rewrite (fun x : Z => Zmult_comm x (Zpower_nat radix n)).
apply ZdividesMult; auto.
case (maxDivUniqueDigit v); auto.
replace (S (maxDiv v (digit radix v) + n)) with
 (S (maxDiv v (digit radix v)) + n); auto.
rewrite Zpower_nat_is_exp.
repeat rewrite (fun x : Z => Zmult_comm x (Zpower_nat radix n)).
red in |- *; intros H'.
absurd (Zdivides v (Zpower_nat radix (S (maxDiv v (digit radix v))))).
case (maxDivUniqueDigit v); auto.
apply ZdividesDiv with (p := Zpower_nat radix n); auto with zarith.
apply digitAdd; auto with zarith.
Qed.
 
Definition LSB (x : float) :=
  (Z_of_nat (maxDiv (Fnum x) (Fdigit radix x)) + Fexp x)%Z.
 
Theorem LSB_shift :
 forall (x : float) (n : nat), ~ is_Fzero x -> LSB x = LSB (Fshift radix n x).
intros x n H'; unfold LSB, Fdigit in |- *; simpl in |- *.
rewrite digitAdd; auto with arith.
rewrite maxDivPlus; auto.
rewrite inj_plus; ring.
Qed.
 
Theorem LSB_comp :
 forall (x y : float) (n : nat), ~ is_Fzero x -> x = y :>R -> LSB x = LSB y.
intros x y H' H'0 H'1.
case (FshiftCorrectSym radix) with (2 := H'1); auto.
intros m1 H'2; elim H'2; intros m2 E; clear H'2.
rewrite (LSB_shift x m1); auto.
rewrite E; auto.
apply sym_equal; apply LSB_shift; auto.
apply (NisFzeroComp radix) with (x := x); auto.
Qed.
 
Theorem maxDiv_opp :
 forall (v : Z) (p : nat), maxDiv v p = maxDiv (- v) p.
intros v p; elim p; simpl in |- *; auto.
intros n H; case (ZdividesP v (radix * Zpower_nat radix n));
 case (ZdividesP (- v) (radix * Zpower_nat radix n)); auto.
intros Z1 Z2; case Z1.
case Z2; intros z1 Hz1; exists (- z1)%Z; rewrite Hz1; ring.
intros Z1 Z2; case Z2.
case Z1; intros z1 Hz1; exists (- z1)%Z.
rewrite <- (Zopp_involutive v); rewrite Hz1; ring.
Qed.
 
Theorem LSB_opp : forall x : float, LSB x = LSB (Fopp x).
intros x; unfold LSB in |- *; simpl in |- *.
rewrite Fdigit_opp; auto.
rewrite maxDiv_opp; auto.
Qed.
 
Theorem maxDiv_abs :
 forall (v : Z) (p : nat), maxDiv v p = maxDiv (Zabs v) p.
intros v p; elim p; simpl in |- *; auto.
intros n H; case (ZdividesP v (radix * Zpower_nat radix n));
 case (ZdividesP (Zabs v) (radix  * Zpower_nat radix n));
 auto.
intros Z1 Z2; case Z1.
case Z2; intros z1 Hz1; exists (Zabs z1); rewrite Hz1.
rewrite Zabs_Zmult; f_equal. apply Zabs_eq. auto with zarith.
intros Z1 Z2; case Z2.
case Z1; intros z1 Hz1.
case (Zle_or_lt v 0); intros Z4.
exists (- z1)%Z; rewrite <- (Zopp_involutive v);
 rewrite <- (Zabs_eq_opp v); auto; rewrite Hz1; ring.
exists z1; rewrite <- (Zabs_eq v); auto with zarith; rewrite Hz1; ring.
Qed.

Theorem LSB_abs : forall x : float, LSB x = LSB (Fabs x).
intros x; unfold LSB in |- *; simpl in |- *.
rewrite Fdigit_abs; auto.
rewrite maxDiv_abs; auto.
Qed.
 
Definition MSB (x : float) := Zpred (Z_of_nat (Fdigit radix x) + Fexp x).
 
Theorem MSB_shift :
 forall (x : float) (n : nat), ~ is_Fzero x -> MSB x = MSB (Fshift radix n x).
intros; unfold MSB, Fshift, Fdigit in |- *; simpl in |- *.
rewrite digitAdd; auto with zarith.
rewrite inj_plus; unfold Zpred in |- *; ring.
Qed.
 
Theorem MSB_comp :
 forall (x y : float) (n : nat), ~ is_Fzero x -> x = y :>R -> MSB x = MSB y.
intros x y H' H'0 H'1.
case (FshiftCorrectSym radix) with (2 := H'1); auto.
intros m1 H'2; elim H'2; intros m2 E; clear H'2.
rewrite (MSB_shift x m1); auto.
rewrite E; auto.
apply sym_equal; apply MSB_shift; auto.
apply (NisFzeroComp radix) with (x := x); auto.
Qed.
 
Theorem MSB_opp : forall x : float, MSB x = MSB (Fopp x).
intros x; unfold MSB in |- *; simpl in |- *.
rewrite Fdigit_opp; auto.
Qed.
 
Theorem MSB_abs : forall x : float, MSB x = MSB (Fabs x).
intros x; unfold MSB in |- *; simpl in |- *.
rewrite Fdigit_abs; auto.
Qed.
 
Theorem LSB_le_MSB : forall x : float, ~ is_Fzero x -> (LSB x <= MSB x)%Z.
intros x H'; unfold LSB, MSB in |- *.
apply Zle_Zpred.
cut (maxDiv (Fnum x) (Fdigit radix x) < Fdigit radix x); auto with zarith.
apply maxDivLt; auto.
unfold Fdigit in |- *; apply NotDividesDigit; auto.
Qed.
 
Theorem Fexp_le_LSB : forall x : float, (Fexp x <= LSB x)%Z.
intros x; unfold LSB in |- *.
auto with zarith.
Qed.
 
Theorem Ulp_Le_LSigB :
 forall x : float, (Float 1%nat (Fexp x) <= Float 1%nat (LSB x))%R.
intros x; apply (oneExp_le radix); auto.
apply Fexp_le_LSB; auto.
Qed.
 
Theorem Fexp_le_MSB : forall x : float, ~ is_Fzero x -> (Fexp x <= MSB x)%Z.
intros x H'; unfold MSB in |- *.
cut (Fdigit radix x <> 0%Z :>Z); unfold Zpred in |- *;
 auto with zarith.
unfold Fdigit in |- *.
red in |- *; intros H'0; absurd (digit radix (Fnum x) = 0); auto with zarith.
apply not_eq_sym; apply lt_O_neq; apply digitNotZero; auto.
Qed.
 
Theorem MSB_le_abs :
 forall x : float, ~ is_Fzero x -> (Float 1%nat (MSB x) <= Fabs x)%R.
intros x H'; unfold MSB, FtoRradix, FtoR in |- *; simpl in |- *.
replace (Zpred (Fdigit radix x + Fexp x)) with
 (Zpred (Fdigit radix x) + Fexp x)%Z; [ idtac | unfold Zpred in |- *; ring ].
rewrite powerRZ_add; auto with real zarith.
rewrite Rmult_1_l.
repeat rewrite (fun r : R => Rmult_comm r (powerRZ radix (Fexp x))).
apply Rmult_le_compat_l; auto with real zarith.
rewrite <- inj_pred; auto with real zarith.
rewrite <- Zpower_nat_Z_powerRZ; auto.
apply Rle_IZR; auto.
unfold Fdigit in |- *; auto with arith.
apply digitLess; auto.
unfold Fdigit in |- *.
apply not_eq_sym; apply lt_O_neq; apply digitNotZero; auto.
Qed.
 
Theorem abs_lt_MSB :
 forall x : float, (Fabs x < Float 1%nat (Zsucc (MSB x)))%R.
intros x.
rewrite (MSB_abs x).
unfold MSB, FtoRradix, FtoR in |- *.
rewrite <- Zsucc_pred; simpl in |- *.
rewrite powerRZ_add; auto with real zarith.
rewrite Rmult_1_l.
repeat rewrite (fun r : R => Rmult_comm r (powerRZ radix (Fexp x))).
apply Rmult_lt_compat_l; auto with real zarith.
rewrite <- Zpower_nat_Z_powerRZ; auto with arith.
apply Rlt_IZR.
unfold Fdigit in |- *; auto with arith.
unfold Fabs in |- *; simpl in |- *.
pattern (Zabs (Fnum x)) at 1 in |- *; rewrite <- (Zabs_eq (Zabs (Fnum x)));
 auto with zarith.
Qed.
 
Theorem LSB_le_abs :
 forall x : float, ~ is_Fzero x -> (Float 1%nat (LSB x) <= Fabs x)%R.
intros x H'; apply Rle_trans with (FtoRradix (Float 1%nat (MSB x))).
apply (oneExp_le radix); auto.
apply LSB_le_MSB; auto.
apply MSB_le_abs; auto.
Qed.
 
Theorem MSB_monotoneAux :
 forall x y : float,
 (Fabs x <= Fabs y)%R -> Fexp x = Fexp y -> (MSB x <= MSB y)%Z.
intros x y H' H'0; unfold MSB in |- *.
rewrite <- H'0.
cut (Fdigit radix x <= Fdigit radix y)%Z;
 [ unfold Zpred in |- *; auto with zarith | idtac ].
unfold Fdigit in |- *; apply inj_le.
apply digit_monotone; auto.
apply le_IZR.
apply Rmult_le_reg_l with (r := powerRZ radix (Fexp x));
 auto with real zarith.
repeat rewrite (Rmult_comm (powerRZ radix (Fexp x))); auto.
pattern (Fexp x) at 2 in |- *; rewrite H'0; auto.
Qed.
 
Theorem MSB_monotone :
 forall x y : float,
 ~ is_Fzero x -> ~ is_Fzero y -> (Fabs x <= Fabs y)%R -> (MSB x <= MSB y)%Z.
intros x y H' H'0 H'1; rewrite (MSB_abs x); rewrite (MSB_abs y).
case (Zle_or_lt (Fexp (Fabs x)) (Fexp (Fabs y))); simpl in |- *; intros Zle1.
rewrite
 MSB_shift with (x := Fabs y) (n := Zabs_nat (Fexp (Fabs y) - Fexp (Fabs x))).
apply MSB_monotoneAux; auto.
unfold FtoRradix in |- *; repeat rewrite Fabs_correct; auto with real arith.
rewrite FshiftCorrect; auto with real arith.
repeat rewrite Fabs_correct; auto with real arith.
repeat rewrite Rabs_Rabsolu; repeat rewrite <- Fabs_correct;
 auto with real arith.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; [ ring | auto with zarith ].
apply Fabs_Fzero; auto.
rewrite
 MSB_shift with (x := Fabs x) (n := Zabs_nat (Fexp (Fabs x) - Fexp (Fabs y))).
apply MSB_monotoneAux; auto.
unfold FtoRradix in |- *; repeat rewrite Fabs_correct; auto with real arith.
rewrite FshiftCorrect; auto with real arith.
repeat rewrite Fabs_correct; auto with real arith.
repeat rewrite Rabs_Rabsolu; repeat rewrite <- Fabs_correct;
 auto with real arith.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; [ ring | auto with zarith ].
apply Fabs_Fzero; auto.
Qed.
 
Theorem MSB_le_multAux :
 forall x y : float,
 ~ is_Fzero x -> ~ is_Fzero y -> (MSB x + MSB y <= MSB (Fmult x y))%Z.
intros x y H' H'0; unfold MSB, Fmult, Fdigit in |- *; simpl in |- *.
replace
 (Zpred (digit radix (Fnum x) + Fexp x) +
  Zpred (digit radix (Fnum y) + Fexp y))%Z with
 (Zpred
    (digit radix (Fnum x) + Zpred (digit radix (Fnum y)) + (Fexp x + Fexp y)));
 [ idtac | unfold Zpred in |- *; ring ].
cut
 (digit radix (Fnum x) + Zpred (digit radix (Fnum y)) <=
  digit radix (Fnum x * Fnum y))%Z;
 [ unfold Zpred in |- *; auto with zarith | idtac ].
rewrite <- inj_pred; auto with float zarith; try rewrite <- inj_plus.
apply inj_le.
rewrite <- digitAdd; auto with zarith.
apply digit_monotone; auto with zarith.
repeat rewrite Zabs_Zmult.
apply Zle_Zmult_comp_l; auto with zarith.
rewrite (fun x => Zabs_eq (Zpower_nat radix x)); auto with zarith.
apply not_eq_sym; apply lt_O_neq; apply digitNotZero; auto.
Qed.
 
Theorem MSB_le_mult :
 forall x y : float,
 ~ is_Fzero x ->
 ~ is_Fzero y ->
 (Fmult (Float 1%nat (MSB x)) (Float 1%nat (MSB y)) <=
  Float 1%nat (MSB (Fmult x y)))%R.
intros x y H' H'0.
rewrite <- oneZplus.
apply (oneExp_le radix); auto.
apply MSB_le_multAux; auto.
Qed.
 
Theorem mult_le_MSBAux :
 forall x y : float,
 ~ is_Fzero x -> ~ is_Fzero y -> (MSB (Fmult x y) <= Zsucc (MSB x + MSB y))%Z.
intros x y H' H'0; unfold MSB, Fmult, Fdigit in |- *; simpl in |- *.
replace
 (Zsucc
    (Zpred (digit radix (Fnum x) + Fexp x) +
     Zpred (digit radix (Fnum y) + Fexp y))) with
 (Zpred (digit radix (Fnum x) + digit radix (Fnum y) + (Fexp x + Fexp y)));
 [ idtac | unfold Zpred, Zsucc in |- *; ring ].
cut
 (digit radix (Fnum x * Fnum y) <=
  digit radix (Fnum x) + digit radix (Fnum y))%Z;
 [ unfold Zpred in |- *; auto with zarith | idtac ].
rewrite <- inj_plus.
apply inj_le; auto.
rewrite <- digitAdd; auto with arith.
apply digit_monotone; auto with arith.
repeat rewrite Zabs_Zmult.
apply Zle_Zmult_comp_l; auto with zarith.
rewrite (fun x => Zabs_eq (Zpower_nat radix x)); auto with zarith.
Qed.
 
Theorem mult_le_MSB :
 forall x y : float,
 ~ is_Fzero x ->
 ~ is_Fzero y ->
 (Float 1%nat (MSB (Fmult x y)) <=
  radix * Fmult (Float 1%nat (MSB x)) (Float 1%nat (MSB y)))%R.
intros x y H' H'0; rewrite <- oneZplus.
replace (radix * Float 1%nat (MSB x + MSB y))%R with
 (FtoRradix (Float 1%nat (Zsucc (MSB x + MSB y)))).
apply (oneExp_le radix); auto.
apply mult_le_MSBAux; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; ring.
Qed.
 
Theorem MSB_mix :
 forall x y : float,
 ~ is_Fzero x ->
 ~ is_Fzero y ->
 (Fabs x * Float 1%nat (MSB y) < radix * (Fabs y * Float 1%nat (MSB x)))%R.
intros x y H' H'0; rewrite (MSB_abs x); rewrite (MSB_abs y).
apply Rle_lt_trans with (Fabs x * Fabs y)%R; auto with real.
apply Rmult_le_compat_l; auto with real.
unfold FtoRradix in |- *; rewrite Fabs_correct; auto with real arith.
rewrite <- MSB_abs; apply MSB_le_abs; auto.
rewrite (Rmult_comm (Fabs x)).
replace (radix * (Fabs y * Float 1%nat (MSB (Fabs x))))%R with
 (Fabs y * (radix * Float 1%nat (MSB (Fabs x))))%R; 
 [ idtac | ring ].
apply Rmult_lt_compat_l; auto with real.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto with real arith.
rewrite Rmult_comm; replace 0%R with (powerRZ radix (Fexp y) * 0)%R;
 [ idtac | ring ].
apply Rmult_lt_compat_l; auto with real arith.
rewrite Zabs_absolu.
replace 0%R with (INR 0); [ idtac | simpl in |- *; auto ];
 rewrite <- INR_IZR_INZ; apply INR_lt_nm.
apply absolu_lt_nz; auto.
replace (radix * Float 1%nat (MSB (Fabs x)))%R with
 (FtoRradix (Float 1%nat (Zsucc (MSB (Fabs x))))).
rewrite <- MSB_abs; apply abs_lt_MSB; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; ring.
Qed.
 
Theorem LSB_rep :
 forall x y : float,
 ~ is_Fzero y ->
 (LSB x <= LSB y)%Z -> exists z : Z, y = Float z (Fexp x) :>R.
intros x y H' H'0.
case (Zle_or_lt (Fexp x) (Fexp y)); intros Zl1.
exists (Fnum y * Zpower_nat radix (Zabs_nat (Fexp y - Fexp x)))%Z.
pattern (Fexp x) at 2 in |- *;
 replace (Fexp x) with (Fexp y - Zabs_nat (Fexp y - Fexp x))%Z.
unfold FtoRradix in |- *;
 rewrite <-
  (FshiftCorrect radix) with (n := Zabs_nat (Fexp y - Fexp x)) (x := y); 
 auto.
rewrite inj_abs; try ring; auto with zarith.
exists (Zquotient (Fnum y) (Zpower_nat radix (Zabs_nat (Fexp x - Fexp y)))).
unfold FtoRradix in |- *;
 rewrite <-
  (FshiftCorrect radix)
                        with
                        (n := Zabs_nat (Fexp x - Fexp y))
                       (x := 
                         Float
                           (Zquotient (Fnum y)
                              (Zpower_nat radix (Zabs_nat (Fexp x - Fexp y))))
                           (Fexp x)); auto.
unfold Fshift in |- *; simpl in |- *.
cut (0 <= Fexp x - Fexp y)%Z;
 [ intros Le1; repeat rewrite inj_abs | auto with zarith ]; 
 auto.
unfold FtoR in |- *; simpl in |- *; auto.
replace (Fexp x - (Fexp x - Fexp y))%Z with (Fexp y); [ idtac | ring ].
replace
 (Zquotient (Fnum y) (Zpower_nat radix (Zabs_nat (Fexp x - Fexp y))) *
  Zpower_nat radix (Zabs_nat (Fexp x - Fexp y)))%Z with (
 Fnum y); auto.
apply ZdividesZquotient; auto with zarith.
apply
 ZdividesTrans
  with (m := Zpower_nat radix (maxDiv (Fnum y) (Fdigit radix y))).
apply maxDivCorrect.
apply ZdividesLessPow; auto.
apply ZleLe.
rewrite inj_abs; auto with zarith.
apply Zplus_le_reg_l with (p := Fexp y).
apply Zle_trans with (LSB x).
replace (Fexp y + (Fexp x - Fexp y))%Z with (Fexp x); [ idtac | ring ].
apply Fexp_le_LSB.
rewrite Zplus_comm; auto.
Qed.
 
Theorem LSB_rep_min :
 forall p : float, exists z : Z, p = Float z (LSB p) :>R.
intros p;
 exists (Zquotient (Fnum p) (Zpower_nat radix (Zabs_nat (LSB p - Fexp p)))).
unfold FtoRradix, FtoR, LSB in |- *; simpl in |- *.
rewrite powerRZ_add; auto with real zarith.
rewrite <- Rmult_assoc.
replace (maxDiv (Fnum p) (Fdigit radix p) + Fexp p - Fexp p)%Z with
 (Z_of_nat (maxDiv (Fnum p) (Fdigit radix p))); auto.
rewrite absolu_INR.
rewrite <- Zpower_nat_Z_powerRZ; auto with zarith.
rewrite <- Rmult_IZR.
rewrite <- ZdividesZquotient; auto with zarith.
apply maxDivCorrect.
ring.
Qed.
End mf.