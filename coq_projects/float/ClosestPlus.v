(****************************************************************************
                                                                             
          IEEE754  :  ClosestPlus                                                   
                                                                             
          Laurent Thery, Sylvie Boldo                                                      
                                                                             
  ******************************************************************************)

Require Export FroundPlus.
Require Export ClosestProp.
Section ClosestP.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem errorBoundedPlusLe :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 (Fexp p <= Fexp q)%Z ->
 Closest b radix (p + q) pq ->
 exists error : float,
   error = Rabs (p + q - pq) :>R /\
   Fbounded b error /\ Fexp error = Zmin (Fexp p) (Fexp q).
intros p q pq H' H'0 H'1 H'2.
cut (ex (fun m : Z => pq = Float m (Fexp (Fplus radix p q)) :>R)).
2: unfold FtoRradix in |- *;
    apply
     RoundedModeRep
      with (b := b) (precision := precision) (P := Closest b radix); 
    auto.
2: apply ClosestRoundedModeP with (precision := precision); auto.
2: rewrite (Fplus_correct radix); auto with arith.
intros H'3; elim H'3; intros m E; clear H'3.
exists
 (Fabs (Fminus radix q (Fminus radix (Float m (Fexp (Fplus radix p q))) p))).
cut (forall A B : Prop, A -> (A -> B) -> A /\ B);
 [ intros tmp; apply tmp; clear tmp | auto ].
unfold FtoRradix in |- *; rewrite Fabs_correct; auto with arith.
cut (forall p q : R, p = q -> Rabs p = Rabs q);
 [ intros tmp; apply tmp; clear tmp | intros p' q' H; rewrite H; auto ].
unfold FtoRradix in |- *; repeat rewrite Fminus_correct; auto with arith.
unfold FtoRradix in E; rewrite E; auto.
ring.
intros H'4.
cut (Rabs (pq - (p + q)) <= Rabs (q - (p + q)))%R.
2: elim H'2; auto.
replace (q - (p + q))%R with (- FtoRradix p)%R.
2: ring.
rewrite Rabs_Ropp.
unfold FtoRradix in |- *; rewrite <- Fabs_correct; auto with arith.
rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr.
unfold FtoRradix in H'4; rewrite <- H'4.
simpl in |- *.
rewrite Zmin_le1; auto.
generalize H'1 H'; case p; case q; unfold Fabs, Fminus, Fopp, Fplus in |- *;
 simpl in |- *; clear H'1 H'.
intros Fnum1 Fexp1 Fnum2 Fexp2 H'5 H'6.
repeat rewrite Zmin_n_n; auto.
repeat rewrite (Zmin_le2 _ _ H'5); auto with zarith.
replace (Zabs_nat (Fexp2 - Fexp2)) with 0.
rewrite Zpower_nat_O.
cut (forall z : Z, (z * 1%nat)%Z = z);
 [ intros tmp; repeat rewrite tmp; clear tmp | auto with zarith ].
unfold FtoRradix, FtoR in |- *; simpl in |- *.
intros H'.
repeat split; simpl in |- *.
rewrite (fun x => Zabs_eq (Zabs x)); auto with zarith.
apply Zle_lt_trans with (Zabs Fnum2); auto.
apply le_IZR.
apply (Rle_monotony_contra_exp radix) with (z := Fexp2); auto.
case H'6; auto.
case H'6; auto.
intros; simpl in |- *; ring.
replace (Fexp2 - Fexp2)%Z with 0%Z; simpl in |- *; auto with zarith.
Qed.
 
Theorem errorBoundedPlusAbs :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) pq ->
 exists error : float,
   error = Rabs (p + q - pq) :>R /\
   Fbounded b error /\ Fexp error = Zmin (Fexp p) (Fexp q).
intros p q pq H' H'0 H'1.
case (Zle_or_lt (Fexp p) (Fexp q)); intros H'2.
apply errorBoundedPlusLe; auto.
replace (p + q)%R with (q + p)%R; [ idtac | ring ].
replace (Zmin (Fexp p) (Fexp q)) with (Zmin (Fexp q) (Fexp p));
 [ idtac | apply Zmin_sym ].
apply errorBoundedPlusLe; auto.
auto with zarith.
apply (ClosestCompatible b radix (p + q)%R (q + p)%R pq); auto.
ring.
case H'1; auto.
Qed.
 
Theorem errorBoundedPlus :
 forall p q pq : float,
 (Fbounded b p) ->
 (Fbounded b q) ->
 (Closest b radix (p + q) pq) ->
 exists error : float,
   error = (p + q - pq)%R :>R /\
   (Fbounded b error) /\ (Fexp error) = (Zmin (Fexp p) (Fexp q)).
intros p q pq H' H'0 H'1.
case (errorBoundedPlusAbs p q pq); auto.
intros x H'2; elim H'2; intros H'3 H'4; elim H'4; intros H'5 H'6;
 clear H'4 H'2.
generalize H'3; clear H'3.
unfold Rabs in |- *; case (Rcase_abs (p + q - pq)).
intros H'2 H'3; exists (Fopp x); split; auto.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto.
unfold FtoRradix in H'3; rewrite H'3; ring.
split.
apply oppBounded; auto.
rewrite <- H'6; auto.
intros H'2 H'3; exists x; split; auto.
Qed.
 
Theorem plusExact1 :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Fexp r <= Zmin (Fexp p) (Fexp q))%Z -> r = (p + q)%R :>R.
intros p q r H' H'0 H'1 H'2.
cut
 (2%nat * Rabs (FtoR radix (Fplus radix p q) - FtoR radix r) <=
  Float 1%nat (Fexp r))%R;
 [ rewrite Fplus_correct; auto with zarith; intros Rl1 | idtac ].
case errorBoundedPlus with (p := p) (q := q) (pq := r); auto.
intros x H'3; elim H'3; intros H'4 H'5; elim H'5; intros H'6 H'7;
 clear H'5 H'3.
unfold FtoRradix in H'4; rewrite <- H'4 in Rl1.
2: apply Rle_trans with (Fulp b radix precision r); auto.
2: apply (ClosestUlp b radix precision); auto.
2: rewrite Fplus_correct; auto with zarith.
2: unfold FtoRradix in |- *; apply FulpLe; auto.
2: apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto.
2: apply ClosestRoundedModeP with (precision := precision); auto.
cut (x = 0%R :>R); [ unfold FtoRradix in |- *; intros Eq1 | idtac ].
replace (FtoR radix r) with (FtoR radix r + 0)%R; [ idtac | ring ].
rewrite <- Eq1.
rewrite H'4; ring.
apply (is_Fzero_rep1 radix).
case (Z_zerop (Fnum x)); simpl in |- *; auto.
intros H'3; Contradict Rl1.
apply Rgt_not_le.
red in |- *; apply Rle_lt_trans with (Rabs (FtoR radix x)).
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
rewrite Rabs_mult.
apply Rmult_le_compat; auto with real arith.
generalize H'3; case (Fnum x); simpl in |- *; auto with real zarith.
intros H'5; case H'5; auto.
intros p0 H'5; rewrite Rabs_right; auto with real.
replace 1%R with (INR 1); unfold IZR; repeat rewrite <- INR_IPR; auto with real arith.
intros p0 H'5; rewrite Faux.Rabsolu_left1; auto.
unfold IZR; rewrite Ropp_involutive.
repeat rewrite <- INR_IPR; simpl; replace 1%R with (INR 1); auto with real arith.
unfold IZR; repeat rewrite <- INR_IPR; replace 0%R with (- 0%nat)%R; auto with real.
rewrite Rabs_right; auto with real arith.
apply Rle_powerRZ; auto with real arith.
auto with zarith.
apply Rle_ge; cut (1 < radix)%Z; auto with float real zarith.
cut (forall r : R, (2%nat * r)%R = (r + r)%R);
 [ intros tmp; rewrite tmp; clear tmp | intros f; simpl in |- *; ring ].
pattern (Rabs (FtoR radix x)) at 1 in |- *;
 replace (Rabs (FtoR radix x)) with (Rabs (FtoR radix x) + 0)%R;
 [ idtac | ring ].
apply Rplus_lt_compat_l; auto.
case (Rabs_pos (FtoR radix x)); auto.
rewrite <- Fabs_correct; auto with arith.
intros H'5; Contradict H'3.
cut (Fnum (Fabs x) = 0%Z).
unfold Fabs in |- *; simpl in |- *; case (Fnum x); simpl in |- *; auto;
 intros; discriminate.
change (is_Fzero (Fabs x)) in |- *.
apply (is_Fzero_rep2 radix); auto with arith.
Qed.
 
Theorem plusExact1bis :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 r <> (p + q)%R :>R -> (Zmin (Fexp p) (Fexp q) < Fexp r)%Z.
intros p0 q0 r0 H' H'0 H'1 H'2;
 case (Zle_or_lt (Fexp r0) (Zmin (Fexp p0) (Fexp q0))); 
 auto.
intros H'3; Contradict H'2.
apply plusExact1; auto.
Qed.
 
Theorem plusExact2Aux :
 forall p q r : float,
 (0 <= p)%R ->
 Fcanonic radix b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Fexp r < Zpred (Fexp p))%Z -> r = (p + q)%R :>R.
intros p q r H' H'0 H'1 H'2 H'3.
apply plusExact1; auto.
apply FcanonicBound with (1 := H'0); auto.
case (Zle_or_lt (Fexp p) (Fexp q)); intros Zl1.
rewrite Zmin_le1; auto with zarith.
apply Zle_trans with (Zpred (Fexp p)); auto with zarith.
unfold Zpred in |- *; auto with zarith.
rewrite Zmin_le2; auto with zarith.
case (Zlt_next _ _ Zl1); intros Zl2.
rewrite Zl2 in H'3.
replace (Fexp q) with (Zpred (Zsucc (Fexp q))); auto with zarith;
 unfold Zpred, Zsucc in |- *; ring.
case H'0; clear H'0; intros H'0.
absurd (r < Float (nNormMin radix precision) (Zpred (Fexp p)))%R.
apply Rle_not_lt; auto.
unfold FtoRradix in |- *;
 apply
  (ClosestMonotone b radix
     (Float (nNormMin radix precision) (Zpred (Fexp p))) (
     p + q)%R); auto; auto.
cut (Float (nNormMin radix precision) (Fexp p) <= p)%R;
 [ intros Eq1 | idtac ].
case (Rle_or_lt 0 q); intros Rl1.
apply Rlt_le_trans with (FtoRradix p).
apply
 Rlt_le_trans with (FtoRradix (Float (nNormMin radix precision) (Fexp p)));
 auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
apply Rmult_lt_compat_l; auto with real arith.
replace 0%R with (IZR 0%nat); auto with real; auto with real float arith.
apply Rlt_IZR; apply nNormPos; auto with zarith.
unfold Zpred in |- *; auto with real float zarith arith.
pattern (FtoRradix p) at 1 in |- *; replace (FtoRradix p) with (p + 0)%R;
 auto with real.
apply Rplus_lt_reg_l with (r := (- q)%R); auto.
replace (- q + (p + q))%R with (FtoRradix p); [ idtac | ring ].
apply
 Rlt_le_trans with (FtoRradix (Float (nNormMin radix precision) (Fexp p)));
 auto.
apply
 Rlt_le_trans
  with (2%nat * Float (nNormMin radix precision) (Zpred (Fexp p)))%R; 
 auto.
cut (forall r : R, (2%nat * r)%R = (r + r)%R);
 [ intros tmp; rewrite tmp; clear tmp | intros; simpl in |- *; ring ].
rewrite (Rplus_comm (- q)).
apply Rplus_lt_compat_l.
rewrite <- Faux.Rabsolu_left1; auto.
rewrite <- (Fabs_correct radix); auto with arith.
unfold FtoRradix in |- *; apply maxMaxBis with (b := b); auto with zarith.
apply Rlt_le; auto.
apply
 Rle_trans with (radix * Float (nNormMin radix precision) (Zpred (Fexp p)))%R.
apply Rmult_le_compat_r; auto.
apply (LeFnumZERO radix); simpl in |- *; auto with arith.
apply Zlt_le_weak; apply nNormPos; auto with zarith.
rewrite INR_IZR_INZ; apply Rle_IZR; simpl in |- *; cut (1 < radix)%Z;
 auto with real zarith.
pattern (Fexp p) at 2 in |- *; replace (Fexp p) with (Zsucc (Zpred (Fexp p)));
 [ idtac | unfold Zsucc, Zpred in |- *; ring ].
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith.
repeat rewrite <- Rmult_assoc.
rewrite (Rmult_comm radix); auto with real.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
apply Rmult_le_compat_r; auto with real zarith.
apply Rle_IZR.
rewrite <- (Zabs_eq (Fnum p)); auto with zarith.
apply pNormal_absolu_min with (b := b); auto with arith.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto.
apply (LeR0Fnum radix); auto with arith.
apply (RoundedModeProjectorIdem b radix (Closest b radix)); auto.
apply ClosestRoundedModeP with (precision := precision); auto.
repeat split; simpl in |- *.
rewrite Zabs_eq; auto with zarith.
apply ZltNormMinVnum; auto with arith.
apply Zlt_le_weak; apply nNormPos; auto with zarith.
apply Zle_trans with (Fexp q); auto with float zarith.
case (Rle_or_lt 0 r); intros Rl1.
rewrite <- (Rabs_right r); auto with real.
rewrite <- (Fabs_correct radix); auto with arith.
unfold FtoRradix in |- *; apply maxMaxBis with (b := b); auto with zarith.
apply
 RoundedModeBounded
  with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
 auto.
apply ClosestRoundedModeP with (precision := precision); auto with real.
apply Rlt_le_trans with 0%R; auto.
apply (LeFnumZERO radix); simpl in |- *; auto with arith.
apply Zlt_le_weak; apply nNormPos; auto with zarith.
absurd (- dExp b <= Fexp q)%Z; auto with float.
apply Zlt_not_le.
case H'0; intros Z1 (Z2, Z3); rewrite <- Z2; auto with zarith.
Qed.
 
Theorem plusExact2 :
 forall p q r : float,
 Fcanonic radix b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Fexp r < Zpred (Fexp p))%Z -> r = (p + q)%R :>R.
intros p q r H' H'0 H'1 H'2.
case (Rle_or_lt 0 p); intros Rl1.
apply plusExact2Aux; auto.
replace (p + q)%R with (- (Fopp p + Fopp q))%R.
rewrite <- (plusExact2Aux (Fopp p) (Fopp q) (Fopp r)); auto.
unfold FtoRradix in |- *; rewrite Fopp_correct; ring.
unfold FtoRradix in |- *; rewrite Fopp_correct.
apply Rlt_le; replace 0%R with (-0)%R; auto with real.
apply FcanonicFopp; auto with arith.
apply oppBounded; auto.
replace (Fopp p + Fopp q)%R with (- (p + q))%R.
apply ClosestOpp; auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; ring.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct; ring.
Qed.
 
Theorem plusExactR0 :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r -> r = 0%R :>R -> r = (p + q)%R :>R.
intros p q r H' H'0 H'1 H'2.
cut (r = FtoRradix (Fzero (- dExp b)) :>R);
 [ intros Eq1; rewrite Eq1
 | rewrite H'2; apply sym_eq; unfold FtoRradix in |- *; apply FzeroisZero ].
apply plusExact1; auto.
apply (ClosestCompatible b radix (p + q)%R (p + q)%R r); auto.
apply FboundedFzero; auto.
simpl in |- *; auto.
unfold Zmin in |- *; case (Fexp p ?= Fexp q)%Z; auto with float.
Qed.
 
Theorem plusErrorBound1 :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 ~ is_Fzero r ->
 (Rabs (r - (p + q)) < Rabs r * / 2%nat * (radix * / pPred (vNum b)))%R.
intros p q r H' H'0 H'1 H'2.
cut (Fcanonic radix b (Fnormalize radix b precision r));
 [ intros tmp; Casec tmp; intros Fs | idtac ].
3: apply FnormalizeCanonic; auto with arith.
3: apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto.
3: apply ClosestRoundedModeP with (precision := precision); auto.
2: rewrite <- (plusExact1 p q (Fnormalize radix b precision r)); auto.
2: unfold FtoRradix in |- *; rewrite FnormalizeCorrect; auto with arith.
2: replace (FtoR radix r - FtoR radix r)%R with 0%R; [ idtac | ring ].
2: rewrite Rabs_R0.
2: replace 0%R with (0 * (radix * / pPred (vNum b)))%R;
    [ apply Rmult_lt_compat_r | ring ].
2: replace 0%R with (0 * / pPred (vNum b))%R;
    [ apply Rmult_lt_compat_r | ring ].
2: apply Rinv_0_lt_compat; replace 0%R with (IZR 0); auto with real zarith.
2: apply Rlt_IZR; unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *.
2: apply vNumbMoreThanOne with (radix := radix) (precision := precision);
    auto with real zarith.
2: cut (1 < radix)%Z; auto with real zarith.
2: replace 0%R with (0 * / 2%nat)%R; [ apply Rmult_lt_compat_r | ring ];
    auto with real.
2: case (Rabs_pos (FtoR radix r)); auto.
2: intros H'3; Contradict H'2.
2: apply is_Fzero_rep2 with (radix := radix); auto with real arith.
2: generalize H'3; fold FtoRradix in |- *; unfold Rabs in |- *;
    case (Rcase_abs r); auto.
2: intros r0 H'2; replace 0%R with (-0)%R; [ rewrite H'2 | idtac ]; ring.
2: apply (ClosestCompatible b radix (p + q)%R (p + q)%R r); auto.
2: apply sym_eq; apply FnormalizeCorrect; auto.
2: apply FnormalizeBounded; auto with arith.
2: apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto.
2: apply ClosestRoundedModeP with (precision := precision); auto.
2: replace (Fexp (Fnormalize radix b precision r)) with (- dExp b)%Z.
2: unfold Zmin in |- *; case (Fexp p ?= Fexp q)%Z; auto with float.
2: apply sym_equal; case Fs; intros H1 H2; case H2; auto.
apply Rle_lt_trans with (/ 2%nat * Fulp b radix precision r)%R.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real; rewrite Rmult_1_l.
unfold FtoRradix in |- *; rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr;
 rewrite <- (Fplus_correct radix); auto with zarith.
apply ClosestUlp; auto.
rewrite Fplus_correct; auto with arith.
replace (Rabs r * / 2%nat * (radix * / pPred (vNum b)))%R with
 (/ 2%nat * (Rabs r * (radix * / pPred (vNum b))))%R;
 [ apply Rmult_lt_compat_l; auto with real | ring ].
replace (Fulp b radix precision r) with
 (Float (pPred (vNum b)) (Zpred (Fexp (Fnormalize radix b precision r))) *
  (radix * / pPred (vNum b)))%R.
apply Rmult_lt_compat_r.
replace 0%R with (radix * 0)%R; [ apply Rmult_lt_compat_l | ring ];
 auto with real arith.
apply Rinv_0_lt_compat; replace 0%R with (IZR 0%nat); auto with real arith;
 apply Rlt_IZR.
unfold pPred in |- *; apply Zlt_succ_pred;
 apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
unfold FtoRradix in |- *;
 rewrite <- (FnormalizeCorrect _ radixMoreThanOne b precision r).
rewrite <- (Fabs_correct radix); auto with arith.
apply FnormalBoundAbs; auto with zarith.
unfold Fulp, FtoRradix, FtoR in |- *; simpl in |- *.
apply
 trans_eq
  with
    (pPred (vNum b) * / pPred (vNum b) *
     (radix * powerRZ radix (Zpred (Fexp (Fnormalize radix b precision r)))))%R;
 [ ring | idtac ]; auto.
rewrite Rinv_r; auto with real arith.
rewrite <- powerRZ_Zs; auto with real.
cut (forall r : Z, Zsucc (Zpred r) = r);
 [ intros Er; rewrite Er | intros r'; unfold Zsucc, Zpred in |- * ]; 
 ring.
apply Rlt_dichotomy_converse; right; red in |- *.
replace 0%R with (IZR 0); cut (1 < radix)%Z; auto with real zarith.
apply Rlt_dichotomy_converse; right; red in |- *.
replace 0%R with (IZR 0); auto with real zarith.
unfold pPred in |- *; apply Rlt_IZR; apply Zlt_succ_pred; simpl in |- *.
apply vNumbMoreThanOne with (radix := radix) (precision := precision);
 auto with real arith.
Qed.
 
Theorem plusErrorBound1bis :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 ~ is_Fzero r ->
 (Rabs (r - (p + q)) <= Rabs r * / 2%nat * (radix * / Zpos (vNum b)))%R.
intros p q r H' H'0 H'1 H'2.
cut (Fcanonic radix b (Fnormalize radix b precision r));
 [ intros tmp; Casec tmp; intros Fs | idtac ].
3: apply FnormalizeCanonic; auto with arith.
3: apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto.
3: apply ClosestRoundedModeP with (precision := precision); auto.
2: rewrite <- (plusExact1 p q (Fnormalize radix b precision r)); auto.
2: unfold FtoRradix in |- *; rewrite FnormalizeCorrect; auto.
2: replace (FtoR radix r - FtoR radix r)%R with 0%R; [ idtac | ring ].
2: rewrite Rabs_R0.
2: replace 0%R with (0 * (radix * / Zpos (vNum b)))%R;
    [ apply Rmult_le_compat_r | ring ]; auto with real zarith.
2: replace 0%R with (0 * / Zpos (vNum b))%R;
    [ apply Rmult_le_compat_r | ring ]; auto with real zarith.
2: replace 0%R with (0 * / 2%nat)%R; [ apply Rmult_le_compat_r | ring ];
    auto with real zarith.
2: apply (ClosestCompatible b radix (p + q)%R (p + q)%R r); auto.
2: apply sym_eq; apply FnormalizeCorrect; auto.
2: apply FnormalizeBounded; auto with arith.
2: apply
    RoundedModeBounded
     with (radix := radix) (P := Closest b radix) (r := (p + q)%R); 
    auto.
2: apply ClosestRoundedModeP with (precision := precision); auto.
2: replace (Fexp (Fnormalize radix b precision r)) with (- dExp b)%Z.
2: unfold Zmin in |- *; case (Fexp p ?= Fexp q)%Z; intuition.
2: case Fs; intros H1 (H2, H3); auto.
apply Rle_trans with (/ 2%nat * Fulp b radix precision r)%R.
replace (Rabs (FtoRradix r - (FtoRradix p + FtoRradix q))) with
 (/ 2%nat * (2%nat * Rabs (FtoRradix r - (FtoRradix p + FtoRradix q))))%R;
 [ idtac | rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real ].
apply Rmult_le_compat_l; auto with real.
replace (FtoRradix r - (FtoRradix p + FtoRradix q))%R with
 (- (FtoRradix p + FtoRradix q - FtoRradix r))%R;
 [ rewrite Rabs_Ropp | ring ].
apply (ClosestUlp b radix); auto.
replace (Rabs r * / 2%nat * (radix * / Zpos (vNum b)))%R with
 (/ 2%nat * (Rabs r * (radix * / Zpos (vNum b))))%R;
 [ apply Rmult_le_compat_l; auto with real | ring ].
replace (Fulp b radix precision r) with
 (Zpos (vNum b) *
  FtoR radix (Float 1%nat (Zpred (Fexp (Fnormalize radix b precision r)))) *
  (radix * / Zpos (vNum b)))%R.
apply Rmult_le_compat_r.
replace 0%R with (radix * 0)%R; [ apply Rmult_le_compat_l | ring ];
 apply Rlt_le; auto with real arith;
rewrite INR_IZR_INZ; apply Rlt_IZR; simpl in |- *; apply Zlt_1_O;
 apply Zlt_le_weak;
 apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
unfold FtoRradix in |- *;
 rewrite <- (FnormalizeCorrect _ radixMoreThanOne b precision r).
rewrite <- (Fabs_correct radix); auto with arith.
apply FnormalBoundAbs2 with precision; auto with arith.
unfold Fulp, FtoRradix, FtoR in |- *; simpl in |- *.
apply
 trans_eq
  with
    (nat_of_P (vNum b) * / nat_of_P (vNum b) *
     (radix * powerRZ radix (Zpred (Fexp (Fnormalize radix b precision r)))))%R;
 [ unfold IZR at 1 5; repeat rewrite <- INR_IPR; ring | idtac].
rewrite Rinv_r; auto with real arith.
rewrite <- powerRZ_Zs; auto with real zarith.
rewrite <- Zsucc_pred; ring.
Qed.
 
Theorem plusErrorBound1withZero :
 forall p q r : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) r ->
 (Rabs (r - (p + q)) <= Rabs r * / 2%nat * (radix * / pPred (vNum b)))%R.
intros p q r H H0 H1.
case (Req_dec r 0); intros Hr.
replace (Rabs (r - (p + q))) with (Rabs r * / 2%nat * 0)%R.
apply Rmult_le_compat_l.
replace 0%R with (Rabs r * 0)%R; [ apply Rmult_le_compat_l | ring ];
 auto with real arith.
replace 0%R with (radix * 0)%R; [ apply Rmult_le_compat_l | ring ];
 auto with real arith.
apply Rlt_le; apply Rinv_0_lt_compat; auto with real arith.
replace 0%R with (IZR 0%nat); auto with real zarith; apply Rlt_IZR.
apply Zle_lt_trans with (nNormMin radix precision).
apply Zlt_le_weak; apply nNormPos; auto with real zarith.
apply nNormMimLtvNum; auto with real zarith.
rewrite <- plusExactR0 with (3 := H1); auto with real zarith.
rewrite Hr; repeat rewrite Rabs_R0 || (rewrite Rminus_diag_eq; auto); ring.
apply Rlt_le; apply plusErrorBound1; auto.
Contradict Hr; unfold FtoRradix in |- *; apply is_Fzero_rep1; auto.
Qed.
 
Theorem pPredMoreThanOne : (0 < pPred (vNum b))%Z.
unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
Qed.
 
Theorem pPredMoreThanRadix : (radix < pPred (vNum b))%Z.
apply Zle_lt_trans with (nNormMin radix precision).
pattern radix at 1 in |- *; rewrite <- (Zpower_nat_1 radix);
 unfold nNormMin in |- *; auto with zarith.
apply nNormMimLtvNum; auto with zarith.
Qed.
 
Theorem RoundBound :
 forall x y p : float,
 Fbounded b x ->
 Fbounded b y ->
 Fbounded b p ->
 Closest b radix (x + y) p ->
 (radix < 2%nat * pPred (vNum b))%Z ->
 (Rabs p <=
  Rabs (x + y) *
  (2%nat * pPred (vNum b) * / (2%nat * pPred (vNum b) - radix)))%R.
intros x y p H H0 H1 H2 H3.
cut (0 < 2%nat * pPred (vNum b))%Z;
 [ intros NZ1 | apply Zlt_trans with radix; auto with zarith ].
cut (0 < 2%nat * pPred (vNum b))%R;
 [ intros NZ1'
 | rewrite INR_IZR_INZ; rewrite <- Rmult_IZR; auto with real zarith ].
cut (radix < 2%nat * pPred (vNum b))%R;
 [ intros NZ2
 | rewrite INR_IZR_INZ; rewrite <- Rmult_IZR; auto with real zarith ].
replace (Rabs p) with
 (Rabs p * ((2%nat * pPred (vNum b) - radix) * / (2%nat * pPred (vNum b))) *
  (2%nat * pPred (vNum b) * / (2%nat * pPred (vNum b) - radix)))%R.
2: replace
    (Rabs p * ((2%nat * pPred (vNum b) - radix) * / (2%nat * pPred (vNum b))) *
     (2%nat * pPred (vNum b) * / (2%nat * pPred (vNum b) - radix)))%R with
    (Rabs p *
     ((2%nat * pPred (vNum b) - radix) * / (2%nat * pPred (vNum b) - radix)) *
     (2%nat * pPred (vNum b) * / (2%nat * pPred (vNum b))))%R;
    [ idtac | ring ].
2: repeat rewrite Rinv_r; auto with real zarith; try ring.
apply Rmult_le_compat_r.
replace 0%R with (2%nat * pPred (vNum b) * 0)%R;
 [ apply Rmult_le_compat_l | ring ]; auto with real zarith.
replace ((2%nat * pPred (vNum b) - radix) * / (2%nat * pPred (vNum b)))%R
 with (1 - radix * / (2%nat * pPred (vNum b)))%R.
2: unfold Rminus in |- *; rewrite Rmult_plus_distr_r; rewrite Rinv_r;
    auto with real.
replace (Rabs p * (1 - radix * / (2%nat * pPred (vNum b))))%R with
 (Rabs p - Rabs p * (radix * / (2%nat * pPred (vNum b))))%R;
 [ idtac | ring; ring ].
apply Rplus_le_reg_l with (Rabs p * (radix * / (2%nat * pPred (vNum b))))%R.
replace
 (Rabs (FtoRradix p) * (radix * / (2%nat * pPred (vNum b))) +
  (Rabs (FtoRradix p) -
   Rabs (FtoRradix p) * (radix * / (2%nat * pPred (vNum b)))))%R with
 (Rabs p); [ idtac | ring ].
apply Rle_trans with (Rabs (p - (x + y)) + Rabs (x + y))%R.
pattern (FtoRradix p) at 1 in |- *;
 replace (FtoRradix p) with (p - (x + y) + (x + y))%R;
 [ apply Rabs_triang | ring ].
rewrite (Rplus_comm (Rabs (p - (x + y))) (Rabs (x + y)));
 rewrite
  (Rplus_comm (Rabs p * (radix * / (2%nat * pPred (vNum b)))) (Rabs (x + y)))
  ; apply Rplus_le_compat_l.
replace (Rabs p * (radix * / (2%nat * pPred (vNum b))))%R with
 (Rabs p * / 2%nat * (radix * / pPred (vNum b)))%R;
 [ apply plusErrorBound1withZero | idtac ]; auto.
rewrite (Rinv_mult_distr 2%nat (pPred (vNum b))); auto with real zarith.
ring.
apply NEq_IZRO; auto with real zarith.
generalize pPredMoreThanOne; auto with zarith.
Qed.
 
Theorem plusExactExp :
 forall p q pq : float,
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (p + q) pq ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fbounded b r /\
       Fbounded b s /\
       s = pq :>R /\
       r = (p + q - s)%R :>R /\
       Fexp r = Zmin (Fexp p) (Fexp q) :>Z /\
       (Fexp r <= Fexp s)%Z /\ (Fexp s <= Zsucc (Zmax (Fexp p) (Fexp q)))%Z)).
intros p q pq H H0 H1.
case (plusExpBound b radix precision) with (P := Closest b radix) (5 := H1);
 auto with zarith.
apply (ClosestRoundedModeP b radix precision); auto with zarith.
intros r (H2, (H3, (H4, H5))); fold FtoRradix in H3.
case (Req_dec (p + q - pq) 0); intros Hr.
cut (Fbounded b (Fzero (Zmin (Fexp p) (Fexp q)))); [ intros Fbs | idtac ].
exists (Fzero (Zmin (Fexp p) (Fexp q))); exists r; repeat (split; auto).
rewrite (FzeroisReallyZero radix); rewrite <- Hr; rewrite <- H3; auto.
case (Zmin_or (Fexp p) (Fexp q)); intros Hz; rewrite Hz;
 apply FboundedZeroSameExp; auto.
case (errorBoundedPlus p q pq); auto.
intros error (H6, (H7, H8)).
exists error; exists r; repeat (split; auto).
rewrite H3; auto.
rewrite H8; auto.
Qed.
 
Theorem plusExactExpCanonic :
 forall c d p q : float,
 Fbounded b c ->
 Fbounded b d ->
 Fbounded b p ->
 Fbounded b q ->
 Closest b radix (c + d) p ->
 q = (c + d - p)%R :>R ->
 q <> 0%R :>R ->
 ex
   (fun r : float =>
    ex
      (fun s : float =>
       Fcanonic radix b s /\
       Fbounded b r /\
       s = p :>R /\
       r = (c + d - s)%R :>R /\
       Fexp r = Zmin (Fexp c) (Fexp d) :>Z /\
       (Fexp r < Fexp s)%Z /\ (Fexp s <= Zsucc (Zmax (Fexp c) (Fexp d)))%Z)).
intros c d p q H H0 H1 H2 H3 H4 H5.
case (plusExactExp c d p); auto.
intros r (s, (H6, (H7, (H8, (H9, (H10, (H11, H12))))))).
exists r; exists (Fnormalize radix b precision s).
repeat (split; auto with float).
apply FnormalizeCanonic; auto with arith.
rewrite <- H8; apply (FnormalizeCorrect radix); auto with zarith.
rewrite (FnormalizeCorrect radix); auto with zarith.
apply
 ClosestErrorExpStrict
  with (radix := radix) (b := b) (precision := precision) (x := (c + d)%R);
 auto with float.
apply FnormalizeBounded; auto with arith.
apply (ClosestCompatible b radix (c + d)%R (c + d)%R p); auto.
rewrite (FnormalizeCorrect radix); auto with zarith.
apply FnormalizeBounded; auto with arith.
rewrite (FnormalizeCorrect radix); auto with zarith.
fold FtoRradix in |- *; rewrite H9; rewrite H8; rewrite <- H4; auto.
apply Zle_trans with (Fexp s); auto.
apply FcanonicLeastExp with radix b precision; auto with arith.
apply sym_eq; apply FnormalizeCorrect; auto with real.
apply FnormalizeCanonic; auto with arith.
Qed.
End ClosestP.
