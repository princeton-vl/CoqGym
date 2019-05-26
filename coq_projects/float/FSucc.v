(****************************************************************************
                                                                             
          IEEE754  :  FSucc                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export List.
Require Export Fnorm.
Section suc.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Definition FSucc (x : float) :=
  match Z_eq_bool (Fnum x) (pPred (vNum b)) with
  | true => Float (nNormMin radix precision) (Zsucc (Fexp x))
  | false =>
      match Z_eq_bool (Fnum x) (- nNormMin radix precision) with
      | true =>
          match Z_eq_bool (Fexp x) (- dExp b) with
          | true => Float (Zsucc (Fnum x)) (Fexp x)
          | false => Float (- pPred (vNum b)) (Zpred (Fexp x))
          end
      | false => Float (Zsucc (Fnum x)) (Fexp x)
      end
  end.
 
Theorem FSuccSimpl1 :
 forall x : float,
 Fnum x = pPred (vNum b) ->
 FSucc x = Float (nNormMin radix precision) (Zsucc (Fexp x)).
intros x H'; unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum x) (pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (pPred (vNum b))); auto.
intros H'0; Contradict H'0; auto.
Qed.
 
Theorem FSuccSimpl2 :
 forall x : float,
 Fnum x = (- nNormMin radix precision)%Z ->
 Fexp x <> (- dExp b)%Z ->
 FSucc x = Float (- pPred (vNum b)) (Zpred (Fexp x)).
intros x H' H'0; unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum x) (pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (pPred (vNum b))); auto.
intros H'1; absurd (0%nat <= pPred (vNum b))%Z; auto with zarith arith.
rewrite <- H'1; rewrite H'.
unfold nNormMin in |- *; simpl in |- *; auto with zarith.
replace 0%Z with (- (0))%Z; auto with zarith.
unfold pPred in |- *; apply Zle_Zpred; auto with zarith.
intros H'1;
 generalize (Z_eq_bool_correct (Fnum x) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (- nNormMin radix precision)).
intros H'2; generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); auto.
intros H'3; Contradict H'0; auto.
intros H'2; Contradict H'2; auto.
Qed.
 
Theorem FSuccSimpl3 :
 FSucc (Float (- nNormMin radix precision) (- dExp b)) =
 Float (Zsucc (- nNormMin radix precision)) (- dExp b).
unfold FSucc in |- *; simpl in |- *.
generalize (Z_eq_bool_correct (- nNormMin radix precision) (pPred (vNum b)));
 case (Z_eq_bool (- nNormMin radix precision) (pPred (vNum b))); 
 auto.
intros H'1; absurd (0%nat <= pPred (vNum b))%Z; auto with zarith arith.
rewrite <- H'1.
unfold nNormMin in |- *; simpl in |- *; auto with zarith.
replace 0%Z with (- (0))%Z; auto with zarith.
unfold pPred in |- *; apply Zle_Zpred; auto with zarith.
intros H';
 generalize
  (Z_eq_bool_correct (- nNormMin radix precision)
     (- nNormMin radix precision));
 case (Z_eq_bool (- nNormMin radix precision) (- nNormMin radix precision)).
intros H'0; generalize (Z_eq_bool_correct (- dExp b) (- dExp b));
 case (Z_eq_bool (- dExp b) (- dExp b)); auto.
intros H'1; Contradict H'1; auto.
intros H'1; Contradict H'1; auto.
Qed.
 
Theorem FSuccSimpl4 :
 forall x : float,
 Fnum x <> pPred (vNum b) ->
 Fnum x <> (- nNormMin radix precision)%Z ->
 FSucc x = Float (Zsucc (Fnum x)) (Fexp x).
intros x H' H'0; unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum x) (pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (pPred (vNum b))); auto.
intros H'1; Contradict H'; auto.
intros H'1;
 generalize (Z_eq_bool_correct (Fnum x) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (- nNormMin radix precision)); 
 auto.
intros H'2; Contradict H'0; auto.
Qed.
 
Theorem FSuccDiff1 :
 forall x : float,
 Fnum x <> (- nNormMin radix precision)%Z ->
 Fminus radix (FSucc x) x = Float 1%nat (Fexp x) :>R.
intros x H'.
generalize (Z_eq_bool_correct (Fnum x) (pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (pPred (vNum b))); intros H'1.
rewrite FSuccSimpl1; auto.
unfold FtoRradix, FtoR, Fminus, Fopp, Fplus in |- *; simpl in |- *; auto.
repeat rewrite Zmin_le2; auto with zarith.
rewrite <- Zminus_succ_l; repeat rewrite <- Zminus_diag_reverse.
rewrite absolu_Zs; auto with zarith; simpl in |- *.
rewrite H'1; unfold pPred in |- *; rewrite pGivesBound;
 unfold nNormMin in |- *.
replace (Zpower_nat radix (pred precision) * (radix * 1))%Z with
 (Zpower_nat radix precision). f_equal. unfold Zpred.
rewrite Z.opp_add_distr. rewrite Z.mul_1_r. rewrite Z.add_assoc. now rewrite Z.add_opp_diag_r.
(*rewrite plus_IZR; rewrite Rmult_IZR; simpl in |- *.
unfold Zpred in |- *; unfold Zminus in |- *; simpl in |- *.
repeat ring_simplify. ring.*) rewrite Z.mul_1_r.
pattern precision at 1 in |- *; replace precision with (pred precision + 1).
rewrite Zpower_nat_is_exp; rewrite Zpower_nat_1; auto.
generalize precisionNotZero; case precision; simpl in |- *;
 auto with zarith arith.
rewrite FSuccSimpl4; auto.
unfold FtoRradix, FtoR, Fminus, Fopp, Fplus in |- *; simpl in |- *; auto.
repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse; simpl in |- *.
repeat rewrite Zmult_1_r.
replace (Zsucc (Fnum x) + - Fnum x)%Z with (Z_of_nat 1).
simpl in |- *; auto.
simpl in |- *; unfold Zsucc in |- *; ring.
Qed.
 
Theorem FSuccDiff2 :
 forall x : float,
 Fnum x = (- nNormMin radix precision)%Z ->
 Fexp x = (- dExp b)%Z -> Fminus radix (FSucc x) x = Float 1%nat (Fexp x) :>R.
intros x H' H'0; replace x with (Float (Fnum x) (Fexp x)).
rewrite H'; rewrite H'0; rewrite FSuccSimpl3; auto.
unfold FtoRradix, FtoR, Fminus, Fopp, Fplus in |- *; simpl in |- *; auto.
repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse;
 auto with zarith.
simpl in |- *; repeat rewrite Zmult_1_r.
rewrite Zplus_succ_l; rewrite Zplus_opp_r; simpl in |- *; auto.
case x; simpl in |- *; auto.
Qed.
 
Theorem FSuccDiff3 :
 forall x : float,
 Fnum x = (- nNormMin radix precision)%Z ->
 Fexp x <> (- dExp b)%Z ->
 Fminus radix (FSucc x) x = Float 1%nat (Zpred (Fexp x)) :>R.
intros x H' H'1; rewrite FSuccSimpl2; auto.
unfold FtoRradix, FtoR, Fminus, Fopp, Fplus in |- *; simpl in |- *; auto.
repeat rewrite Zmin_le1; auto with zarith.
rewrite <- Zminus_diag_reverse; rewrite <- Zminus_n_predm;
 repeat rewrite <- Zminus_diag_reverse.
rewrite absolu_Zs; auto with zarith; simpl in |- *.
rewrite H'; unfold pPred in |- *; rewrite pGivesBound;
 unfold nNormMin in |- *.
rewrite Zopp_involutive; repeat rewrite Zmult_1_r.
replace (Zpower_nat radix (pred precision) * radix)%Z with
 (Zpower_nat radix precision).
unfold Zpred in |- *; simpl in |- *;
 repeat rewrite plus_IZR || rewrite Ropp_Ropp_IZR. f_equal.
simpl in |- *; ring.
pattern precision at 1 in |- *; replace precision with (pred precision + 1).
rewrite Zpower_nat_is_exp; rewrite Zpower_nat_1; auto.
generalize precisionNotZero; case precision; simpl in |- *;
 auto with zarith arith.
Qed.
 
Theorem ZltNormMinVnum : (nNormMin radix precision < Zpos (vNum b))%Z.
unfold nNormMin in |- *; rewrite pGivesBound; auto with zarith.
Qed.
Hint Resolve ZltNormMinVnum: float.
 
Theorem FSuccNormPos :
 forall a : float,
 (0 <= a)%R -> Fnormal radix b a -> Fnormal radix b (FSucc a).
intros a H' H'0; unfold FSucc in |- *.
cut (Fbounded b a);
 [ intros B0 | apply FnormalBounded with (1 := H'0); auto ].
generalize (Z_eq_bool_correct (Fnum a) (pPred (vNum b)));
 case (Z_eq_bool (Fnum a) (pPred (vNum b))); auto.
intros H'3; repeat split; simpl in |- *; auto.
rewrite Zabs_eq; auto with float zarith.
unfold nNormMin in |- *; auto with zarith.
apply Zle_trans with (m := Fexp a); auto with float zarith arith.
rewrite pGivesBound; rewrite Zabs_eq; auto with zarith.
pattern precision at 1 in |- *; replace precision with (1 + pred precision).
rewrite Zpower_nat_is_exp; rewrite Zpower_nat_1; unfold nNormMin in |- *;
 auto with zarith.
generalize precisionNotZero; case precision; auto with zarith.
apply Zle_mult_gen; simpl in |- *; auto with zarith.
apply Zle_trans with 1%Z; auto with zarith.
unfold nNormMin in |- *; auto with zarith.
intros H'3;
 generalize (Z_eq_bool_correct (Fnum a) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum a) (- nNormMin radix precision)).
intros H'4; absurd (0 <= Fnum a)%Z; auto.
2: apply LeR0Fnum with (radix := radix); auto with zarith.
rewrite H'4; auto.
apply Zlt_not_le.
replace 0%Z with (- 0%nat)%Z; unfold nNormMin in |- *; auto with zarith.
intros H'4; repeat split; simpl in |- *; auto with float zarith arith.
apply Zle_lt_trans with (Zsucc (Zabs (Fnum a))); auto with float zarith.
case (Zlt_next (Zabs (Fnum a)) (Zpos (vNum b)));
 auto with float zarith arith.
intros H1; Contradict H'3.
unfold pPred in |- *; rewrite H1; rewrite Zabs_eq; auto with zarith.
apply LeR0Fnum with (radix := radix); auto with zarith.
apply Zle_trans with (Zabs (radix * Fnum a)); auto with float zarith.
case H'0; auto.
repeat rewrite Zabs_Zmult.
cut (0 <= Fnum a)%Z; [ intros Z1 | apply LeR0Fnum with (radix := radix) ];
 auto.
rewrite (Zabs_eq (Fnum a)); auto.
rewrite (Zabs_eq (Zsucc (Fnum a))); auto with zarith.
Qed.
 
Theorem FSuccSubnormNotNearNormMin :
 forall a : float,
 Fsubnormal radix b a ->
 Fnum a <> Zpred (nNormMin radix precision) -> Fsubnormal radix b (FSucc a).
intros a H' H'0.
cut (Fbounded b a);
 [ intros B0 | apply FsubnormalFbounded with (1 := H'); auto ].
unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum a) (pPred (vNum b)));
 case (Z_eq_bool (Fnum a) (pPred (vNum b))); auto.
intros H'2; absurd (Fdigit radix a < precision); auto with float.
2: apply FsubnormalDigit with (b := b); auto.
unfold Fdigit in |- *; rewrite H'2.
unfold pPred in |- *;
 rewrite
  (digitPredVNumiSPrecision radix) with (b := b) (precision := precision);
 auto with arith.
intros H'3;
 generalize (Z_eq_bool_correct (Fnum a) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum a) (- nNormMin radix precision)).
intros H'2; absurd (Fdigit radix a < precision); auto with float.
unfold Fdigit in |- *; rewrite H'2.
replace (digit radix (- nNormMin radix precision)) with
 (digit radix (nNormMin radix precision)).
rewrite digitnNormMin; auto with arith.
case (nNormMin radix precision); simpl in |- *; auto.
apply FsubnormalDigit with (b := b); auto.
intros H'4; repeat split; simpl in |- *; auto with float zarith arith.
apply Zle_lt_trans with (m := Zsucc (Zabs (Fnum a)));
 auto with float zarith arith.
apply Zlt_le_trans with (m := Zsucc (nNormMin radix precision));
 auto with float zarith arith.
apply Zsucc_lt_compat; apply pSubnormal_absolu_min with (3 := pGivesBound);
 auto with float zarith arith.
case H'; intros H1 (H2, H3); auto with float.
rewrite Zabs_Zmult.
rewrite (Zabs_eq radix); auto with zarith.
apply Zlt_le_trans with (m := (radix * nNormMin radix precision)%Z);
 auto with float zarith arith.
apply Zmult_gt_0_lt_compat_l; try apply Zlt_gt; auto with zarith.
apply Zlt_Zabs_Zpred; auto with float zarith arith.
apply pSubnormal_absolu_min with (3 := pGivesBound); auto.
pattern radix at 1 in |- *; rewrite <- (Zpower_nat_1 radix);
 unfold nNormMin in |- *; rewrite <- Zpower_nat_is_exp.
rewrite pGivesBound.
generalize precisionNotZero; case precision; simpl in |- *; auto with zarith.
Qed.
 
Theorem FSuccSubnormNearNormMin :
 forall a : float,
 Fsubnormal radix b a ->
 Fnum a = Zpred (nNormMin radix precision) -> Fnormal radix b (FSucc a).
intros a H' H'0.
cut (Fbounded b a); [ intros Fb0 | apply FsubnormalFbounded with (1 := H') ].
unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum a) (pPred (vNum b)));
 case (Z_eq_bool (Fnum a) (pPred (vNum b))); auto.
intros H'1; absurd (nNormMin radix precision < Zpos (vNum b))%Z;
 auto with float.
apply Zle_not_lt.
apply Zle_n_Zpred; unfold pPred in H'1; rewrite <- H'1; rewrite H'0;
 auto with zarith.
intros H'3;
 generalize (Z_eq_bool_correct (Fnum a) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum a) (- nNormMin radix precision)).
intros H'1;
 absurd (- nNormMin radix precision < Zpred (nNormMin radix precision))%Z.
rewrite <- H'1; rewrite <- H'0; auto with zarith.
unfold nNormMin in |- *; apply Zlt_le_trans with (m := (- (0))%Z);
 auto with zarith.
intros H'4; repeat split; simpl in |- *; auto with float zarith arith.
rewrite H'0.
rewrite <- Zsucc_pred.
rewrite Zabs_eq; auto with float zarith.
unfold nNormMin in |- *; auto with zarith.
rewrite H'0.
rewrite <- Zsucc_pred.
pattern radix at 1 in |- *; rewrite <- (Zpower_nat_1 radix);
 unfold nNormMin in |- *; rewrite <- Zpower_nat_is_exp.
rewrite pGivesBound.
generalize precisionNotZero; case precision; simpl in |- *; auto with zarith.
Qed.
 
Theorem FBoundedSuc : forall f : float, Fbounded b f -> Fbounded b (FSucc f).
intros f H'; unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum f) (pPred (vNum b)));
 case (Z_eq_bool (Fnum f) (pPred (vNum b))); intros H'1.
repeat split; simpl in |- *; auto with zarith arith.
rewrite Zabs_eq; auto with float zarith.
unfold nNormMin in |- *; auto with zarith.
apply Zle_trans with (Fexp f); auto with float zarith.
generalize (Z_eq_bool_correct (Fnum f) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum f) (- nNormMin radix precision)); 
 intros H'2.
generalize (Z_eq_bool_correct (Fexp f) (- dExp b));
 case (Z_eq_bool (Fexp f) (- dExp b)); intros H'3.
repeat split; simpl in |- *; auto with float zarith arith.
apply Zlt_Zabs_Zpred; auto with float zarith arith.
repeat split; simpl in |- *; auto with float zarith arith.
rewrite Zabs_Zopp.
rewrite Zabs_eq; unfold pPred in |- *; auto with zarith.
case (Zle_next (- dExp b) (Fexp f)); auto with float zarith arith.
repeat split; simpl in |- *; auto with float zarith arith.
apply Zlt_Zabs_Zpred; auto with float zarith arith.
Qed.
 
Theorem FSuccSubnormal :
 forall a : float, Fsubnormal radix b a -> Fcanonic radix b (FSucc a).
intros a H'.
generalize (Z_eq_bool_correct (Fnum a) (Zpred (nNormMin radix precision)));
 case (Z_eq_bool (Fnum a) (Zpred (nNormMin radix precision))); 
 intros H'1.
left; apply FSuccSubnormNearNormMin; auto.
right; apply FSuccSubnormNotNearNormMin; auto.
Qed.
 
Theorem FSuccPosNotMax :
 forall a : float,
 (0 <= a)%R -> Fcanonic radix b a -> Fcanonic radix b (FSucc a).
intros a H' H'0; case H'0; intros H'2.
left; apply FSuccNormPos; auto.
apply FSuccSubnormal; auto.
Qed.
 
Theorem FSuccNormNegNotNormMin :
 forall a : float,
 (a <= 0)%R ->
 Fnormal radix b a ->
 a <> Float (- nNormMin radix precision) (- dExp b) ->
 Fnormal radix b (FSucc a).
intros a H' H'0 H'1; cut (Fbounded b a);
 [ intros Fb0 | apply FnormalBounded with (1 := H'0) ].
cut (Fnum a <= 0)%Z; [ intros Z0 | apply R0LeFnum with (radix := radix) ];
 auto with zarith.
case (Zle_lt_or_eq _ _ Z0); intros Z1.
2: absurd (is_Fzero a); auto with float.
2: apply FnormalNotZero with (1 := H'0); auto.
unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum a) (pPred (vNum b)));
 case (Z_eq_bool (Fnum a) (pPred (vNum b))); auto.
intros H'2; absurd (0 < Fnum a)%Z; auto with zarith arith.
rewrite H'2; unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *;
 apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith arith.
intros H'3;
 generalize (Z_eq_bool_correct (Fnum a) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum a) (- nNormMin radix precision)); 
 auto.
intros H'2; generalize (Z_eq_bool_correct (Fexp a) (- dExp b));
 case (Z_eq_bool (Fexp a) (- dExp b)).
intros H'4; Contradict H'1; auto.
apply floatEq; auto.
intros H'4; repeat split; simpl in |- *; auto with zarith.
rewrite Zabs_Zopp.
unfold pPred in |- *; rewrite Zabs_eq; auto with zarith.
case (Zle_next (- dExp b) (Fexp a)); auto with float zarith.
rewrite <- Zopp_mult_distr_r; rewrite Zabs_Zopp.
rewrite Zabs_Zmult.
repeat rewrite Zabs_eq; auto with float zarith.
pattern (Zpos (vNum b)) at 1 in |- *;
 rewrite (PosNormMin radix) with (precision := precision); 
 auto with zarith.
apply Zle_Zmult_comp_l; auto with zarith.
unfold pPred in |- *; apply Zle_Zpred; auto with float zarith.
unfold pPred in |- *; apply Zle_Zpred; auto with float zarith.
intros H'2; repeat split; simpl in |- *; auto with float zarith arith.
apply Zlt_trans with (Zabs (Fnum a)); auto with float zarith.
repeat rewrite Zabs_eq_opp; auto with float zarith.
rewrite Zabs_Zmult.
rewrite (Zabs_eq radix);
 [ idtac | apply Zle_trans with 1%Z; auto with zarith ].
repeat rewrite Zabs_eq_opp; auto with float zarith.
pattern (Zpos (vNum b)) at 1 in |- *;
 rewrite (PosNormMin radix) with (precision := precision); 
 auto with zarith.
apply Zle_Zmult_comp_l; auto with zarith.
replace (- Zsucc (Fnum a))%Z with (Zpred (- Fnum a)).
auto with float zarith.
unfold pPred in |- *; apply Zle_Zpred.
case (Zle_lt_or_eq (nNormMin radix precision) (- Fnum a)); auto.
rewrite <- Zabs_eq_opp; auto with float zarith.
apply pNormal_absolu_min with (b := b); auto.
intros H'4; Contradict H'2; rewrite H'4; ring.
apply Zpred_Zopp_Zs; auto.
Qed.
 
Theorem FSuccNormNegNormMin :
 Fsubnormal radix b (FSucc (Float (- nNormMin radix precision) (- dExp b))).
unfold FSucc in |- *; simpl in |- *.
generalize (Z_eq_bool_correct (- nNormMin radix precision) (pPred (vNum b)));
 case (Z_eq_bool (- nNormMin radix precision) (pPred (vNum b))); 
 intros H'; auto.
absurd (0%nat < pPred (vNum b))%Z; auto.
rewrite <- H'; auto with float zarith.
replace (Z_of_nat 0) with (- (0))%Z; [ idtac | simpl in |- *; auto ].
apply Zle_not_lt; apply Zle_Zopp; auto with float zarith.
apply Zlt_le_weak; auto with float zarith.
apply nNormPos; auto with float zarith.
unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *;
 auto with float zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with float zarith.
generalize
 (Z_eq_bool_correct (- nNormMin radix precision) (- nNormMin radix precision));
 case (Z_eq_bool (- nNormMin radix precision) (- nNormMin radix precision));
 intros H'0.
2: Contradict H'0; auto.
generalize (Z_eq_bool_correct (- dExp b) (- dExp b));
 case (Z_eq_bool (- dExp b) (- dExp b)); intros H'1.
2: Contradict H'1; auto.
repeat split; simpl in |- *; auto with zarith.
apply Zle_lt_trans with (m := nNormMin radix precision);
 auto with float zarith.
rewrite <- Zopp_Zpred_Zs; rewrite Zabs_Zopp; rewrite Zabs_eq;
 auto with float zarith.
apply Zle_Zpred; simpl in |- *; auto with float zarith.
apply nNormPos; auto with float zarith.
rewrite Zabs_Zmult; rewrite (Zabs_eq radix); auto with zarith.
rewrite (PosNormMin radix) with (precision := precision); auto with zarith.
apply Zmult_gt_0_lt_compat_l; auto with float zarith.
rewrite <- Zopp_Zpred_Zs; rewrite Zabs_Zopp.
rewrite Zabs_eq; auto with zarith.
apply Zle_Zpred; simpl in |- *; auto with float zarith.
apply nNormPos; auto with float zarith.
Qed.
 
Theorem FSuccNegCanonic :
 forall a : float,
 (a <= 0)%R -> Fcanonic radix b a -> Fcanonic radix b (FSucc a).
intros a H' H'0; case H'0; intros H'1.
case (floatDec a (Float (- nNormMin radix precision) (- dExp b))); intros H'2.
rewrite H'2; right; apply FSuccNormNegNormMin; auto.
left; apply FSuccNormNegNotNormMin; auto.
apply FSuccSubnormal; auto.
Qed.
 
Theorem FSuccCanonic :
 forall a : float, Fcanonic radix b a -> Fcanonic radix b (FSucc a).
intros a H'.
case (Rle_or_lt 0 a); intros H'3.
apply FSuccPosNotMax; auto.
apply FSuccNegCanonic; auto with real.
Qed.
 
Theorem FSuccLt : forall a : float, (a < FSucc a)%R.
intros a; unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum a) (pPred (vNum b)));
 case (Z_eq_bool (Fnum a) (pPred (vNum b))); auto.
intros H'; unfold FtoRradix, FtoR in |- *; simpl in |- *; rewrite H'.
unfold pPred in |- *;
 rewrite (PosNormMin radix) with (precision := precision); 
 auto with zarith; unfold nNormMin in |- *.
rewrite powerRZ_Zs; auto with real zarith.
repeat rewrite <- Rmult_assoc.
apply Rlt_monotony_exp; auto with zarith.
rewrite Zmult_comm.
rewrite <- Rmult_IZR.
apply Rlt_IZR; auto with zarith.
intros H';
 generalize (Z_eq_bool_correct (Fnum a) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum a) (- nNormMin radix precision)).
intros H'0; generalize (Z_eq_bool_correct (Fexp a) (- dExp b));
 case (Z_eq_bool (Fexp a) (- dExp b)).
intros H'1; unfold FtoRradix, FtoR in |- *; simpl in |- *.
apply Rlt_monotony_exp; auto with real zarith.
intros H'1; unfold FtoRradix, FtoR in |- *; simpl in |- *; rewrite H'0.
pattern (Fexp a) at 1 in |- *; replace (Fexp a) with (Zsucc (Zpred (Fexp a))).
rewrite powerRZ_Zs; auto with real zarith.
repeat rewrite <- Rmult_assoc.
apply Rlt_monotony_exp; auto with real zarith.
rewrite <- Rmult_IZR.
apply Rlt_IZR; auto with zarith.
rewrite <- Zopp_mult_distr_l.
apply Zlt_Zopp.
rewrite Zmult_comm.
unfold pPred in |- *;
 rewrite (PosNormMin radix) with (precision := precision); 
 auto with zarith.
apply sym_equal; apply Zsucc_pred.
intros H'1; unfold FtoRradix, FtoR in |- *; simpl in |- *;
 auto with real zarith.
Qed.
 
Theorem FSuccPropPos :
 forall x y : float,
 (0 <= x)%R ->
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (FSucc x <= y)%R.
intros x y H' H'0 H'1 H'2.
cut (Fbounded b x); [ intros Fb0 | apply FcanonicBound with (1 := H'0) ].
cut (Fbounded b y); [ intros Fb1 | apply FcanonicBound with (1 := H'1) ].
case FcanonicLtPos with (p := x) (q := y) (3 := pGivesBound); auto.
case (Z_eq_dec (Fnum x) (pPred (vNum b))); intros H'4.
rewrite FSuccSimpl1; auto.
intros H'5; case (Zlt_next _ _ H'5); intros H'6.
replace y with (Float (Fnum y) (Fexp y)).
rewrite H'6.
generalize Fle_Zle; unfold Fle, FtoRradix in |- *; intros H'7; apply H'7;
 clear H'7; auto with arith.
rewrite <- (Zabs_eq (Fnum y)); auto with float zarith.
apply pNormal_absolu_min with (b := b); auto.
case H'1; auto with float.
intros H'7; Contradict H'5; apply Zle_not_lt.
replace (Fexp y) with (- dExp b)%Z; auto with float.
case H'7; intros H'8 (H'9, H'10); auto.
apply LeR0Fnum with (radix := radix); auto with zarith.
apply Rle_trans with (r2 := FtoR radix x); auto with real.
case y; auto.
apply Rlt_le; auto.
unfold FtoRradix in |- *; apply FcanonicPosFexpRlt with (3 := pGivesBound);
 auto.
apply LeFnumZERO with (radix := radix); auto with zarith.
simpl in |- *; auto with zarith.
apply Zlt_le_weak; apply nNormPos.
auto with zarith.
apply Rle_trans with (r2 := FtoR radix x); auto with real.
rewrite <- FSuccSimpl1; auto.
apply FSuccCanonic; auto.
intros H'5; apply Rlt_le.
unfold FtoRradix in |- *; apply FcanonicPosFexpRlt with (3 := pGivesBound);
 auto.
apply Rle_trans with (r2 := FtoR radix x); auto.
apply Rlt_le; auto.
apply FSuccLt; auto.
apply Rle_trans with (r2 := FtoR radix x); auto with real.
apply FSuccCanonic; auto.
rewrite FSuccSimpl4; auto.
apply sym_not_equal; apply Zlt_not_eq.
apply Zlt_le_trans with (m := 0%Z); auto with zarith.
replace 0%Z with (- 0%nat)%Z; auto with zarith.
apply Zlt_Zopp.
apply nNormPos; auto.
apply LeR0Fnum with (radix := radix); auto with zarith.
intros H'4; elim H'4; intros H'5 H'6; clear H'4.
generalize (Z_eq_bool_correct (Fnum x) (Zpos (vNum b)));
 case (Z_eq_bool (Fnum x) (Zpos (vNum b))); 
 intros H'4.
Contradict H'6; auto.
apply Zle_not_lt; apply Zlt_le_weak.
rewrite H'4; auto with float zarith.
rewrite <- (Zabs_eq (Fnum y)); auto with float zarith.
apply LeR0Fnum with (radix := radix); auto with zarith.
apply Rle_trans with (FtoRradix x); auto with real.
case (Zlt_next _ _ H'6); intros H'7.
rewrite FSuccSimpl4; auto.
rewrite <- H'7; rewrite H'5; unfold FtoRradix, FtoR in |- *; simpl in |- *;
 auto with real.
apply Zlt_not_eq.
unfold pPred in |- *; apply Zlt_succ_pred; rewrite <- H'7; auto with float.
rewrite <- (Zabs_eq (Fnum y)); auto with float zarith.
apply LeR0Fnum with (radix := radix); auto with zarith.
apply Rle_trans with (FtoRradix x); auto with real.
apply Zlt_not_eq_rev.
apply Zlt_le_trans with (m := 0%Z); auto with zarith.
replace 0%Z with (- 0%nat)%Z; auto with zarith.
apply Zlt_Zopp.
apply nNormPos; auto.
apply LeR0Fnum with (radix := radix); auto with zarith.
rewrite FSuccSimpl4; auto.
replace y with (Float (Fnum y) (Fexp y)).
rewrite H'5.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto with real float.
case y; simpl in |- *; auto.
Contradict H'7; auto.
apply Zle_not_lt; apply Zlt_le_weak.
rewrite H'7; auto with float zarith.
unfold pPred in |- *; rewrite <- Zsucc_pred.
rewrite <- (Zabs_eq (Fnum y)); auto with float zarith.
apply LeR0Fnum with (radix := radix); auto with zarith.
apply Rle_trans with (FtoRradix x); auto with real.
apply Zlt_not_eq_rev.
apply Zlt_le_trans with (m := 0%Z); auto with zarith.
replace 0%Z with (- 0%nat)%Z; auto with zarith.
apply Zlt_Zopp.
apply nNormPos; auto.
apply LeR0Fnum with (radix := radix); auto with zarith.
Qed.
 
Theorem R0RltRleSucc : forall x : float, (x < 0)%R -> (FSucc x <= 0)%R.
intros a H'; unfold FSucc in |- *.
generalize (Z_eq_bool_correct (Fnum a) (pPred (vNum b)));
 case (Z_eq_bool (Fnum a) (pPred (vNum b))); auto.
intros H'0; absurd (Fnum a < 0)%Z; auto.
rewrite H'0; auto with zarith arith.
apply Zle_not_lt; unfold pPred in |- *; apply Zle_Zpred; auto with float.
apply Zlt_trans with 1%Z; auto with zarith;
 apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
apply R0LtFnum with (radix := radix); auto with zarith.
generalize (Z_eq_bool_correct (Fnum a) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum a) (- nNormMin radix precision)); 
 intros H'1.
generalize (Z_eq_bool_correct (Fexp a) (- dExp b));
 case (Z_eq_bool (Fexp a) (- dExp b)); intros H'2.
intros H'0.
apply LeZEROFnum with (radix := radix); simpl in |- *; auto with zarith.
apply Zlt_le_succ.
apply R0LtFnum with (radix := radix); auto with zarith.
intros H'0.
apply LeZEROFnum with (radix := radix); simpl in |- *; auto with zarith.
replace 0%Z with (- (0))%Z; [ apply Zle_Zopp | simpl in |- *; auto ].
unfold pPred in |- *; apply Zle_Zpred; apply Zlt_trans with 1%Z;
 auto with zarith;
 apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
intros H'0.
apply LeZEROFnum with (radix := radix); simpl in |- *; auto with zarith.
apply Zlt_le_succ.
apply R0LtFnum with (radix := radix); auto with zarith.
Qed.
 
Theorem FSuccPropNeg :
 forall x y : float,
 (x < 0)%R ->
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (FSucc x <= y)%R.
intros x y H' H'0 H'1 H'2.
cut (Fbounded b x); [ intros Fb0 | apply FcanonicBound with (1 := H'0) ].
cut (Fbounded b y); [ intros Fb1 | apply FcanonicBound with (1 := H'1) ].
case (Rle_or_lt 0 y); intros Rle0.
apply Rle_trans with (r2 := 0%R); auto.
apply R0RltRleSucc; auto.
cut (Fnum x <> pPred (vNum b)); [ intros N0 | idtac ]; auto with zarith.
generalize (Z_eq_bool_correct (Fnum x) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (- nNormMin radix precision)); 
 intros H'4.
generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); intros H'5.
replace x with (Float (Fnum x) (Fexp x)).
rewrite H'4; rewrite H'5; rewrite FSuccSimpl3; auto.
case FcanonicLtNeg with (p := x) (q := y) (3 := pGivesBound); auto with real.
intros H'6; Contradict H'6; rewrite H'5; apply Zle_not_lt; auto with float.
intros H'6; elim H'6; intros H'7 H'8; clear H'6;
 replace y with (Float (Fnum y) (Fexp y)).
rewrite <- H'7; rewrite H'5.
generalize Fle_Zle; unfold Fle, FtoRradix in |- *; intros H'9; apply H'9;
 clear H'9; auto with arith.
rewrite <- H'4; auto with zarith.
case y; auto.
case x; auto.
rewrite FSuccSimpl2; auto.
case FcanonicLtNeg with (p := x) (q := y) (3 := pGivesBound); auto with real.
intros H'6; replace y with (Float (Fnum y) (Fexp y)).
case (Zlt_next _ _ H'6); intros H'7.
rewrite H'7.
rewrite <- Zpred_succ.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
apply Rle_monotone_exp; auto with zarith.
rewrite <- (Zopp_involutive (Fnum y)); apply Rle_IZR; apply Zle_Zopp.
unfold pPred in |- *; apply Zle_Zpred; rewrite <- Zabs_eq_opp;
 auto with float zarith.
apply Zlt_le_weak; apply R0LtFnum with (radix := radix); auto with zarith.
apply Rlt_le; auto with real.
unfold FtoRradix in |- *; apply FcanonicNegFexpRlt with (3 := pGivesBound);
 auto.
apply Rlt_le; auto.
rewrite <- FSuccSimpl2; auto.
apply R0RltRleSucc; auto.
rewrite <- FSuccSimpl2; auto.
apply FSuccCanonic; auto.
simpl in |- *; auto.
apply Zsucc_lt_reg; auto.
rewrite <- Zsucc_pred; auto with zarith.
case y; auto.
intros H'6; elim H'6; intros H'7 H'8; clear H'6; apply Rlt_le.
Contradict H'8; rewrite H'4.
apply Zle_not_lt.
replace (Fnum y) with (- Zabs (Fnum y))%Z.
apply Zle_Zopp.
apply pNormal_absolu_min with (3 := pGivesBound); auto.
case H'1; auto.
intros H'6; Contradict H'5; rewrite H'7; auto with float.
apply FsubnormalFexp with (1 := H'6).
rewrite Zabs_eq_opp.
ring.
apply R0LeFnum with (radix := radix); auto with zarith.
apply Rlt_le; auto.
rewrite FSuccSimpl4; auto.
case FcanonicLtNeg with (p := x) (q := y) (3 := pGivesBound); auto.
apply Rlt_le; auto with real.
intros H'5; apply Rlt_le; auto.
unfold FtoRradix in |- *; apply FcanonicNegFexpRlt with (3 := pGivesBound);
 auto.
apply Rlt_le; auto.
rewrite <- FSuccSimpl4; auto.
apply R0RltRleSucc; auto.
rewrite <- FSuccSimpl4; auto.
apply FSuccCanonic; auto.
intros H'5; elim H'5; intros H'6 H'7; clear H'5.
replace y with (Float (Fnum y) (Fexp y)).
rewrite H'6.
generalize Fle_Zle; unfold Fle, FtoRradix in |- *; intros H'8; apply H'8;
 clear H'8; auto with zarith arith.
case y; auto.
apply Zlt_not_eq.
apply Zlt_trans with 0%Z; auto with zarith.
apply R0LtFnum with (radix := radix); auto with zarith.
unfold pPred in |- *; apply Zlt_succ_pred.
replace (Zsucc 0) with (Z_of_nat 1);
 [ apply (vNumbMoreThanOne radix) with (precision := precision)
 | simpl in |- * ]; auto with zarith.
Qed.
 
Theorem FSuccProp :
 forall x y : float,
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (FSucc x <= y)%R.
intros x y H' H'0 H'1; case (Rle_or_lt 0 x); intros H'2.
apply FSuccPropPos; auto.
apply FSuccPropNeg; auto.
Qed.
 
Theorem FSuccZleEq :
 forall p q : float,
 (p <= q)%R -> (q < FSucc p)%R -> (Fexp p <= Fexp q)%Z -> p = q :>R.
intros p q H'.
generalize (Z_eq_bool_correct (Fnum p) (pPred (vNum b)));
 case (Z_eq_bool (Fnum p) (pPred (vNum b))); intros H'0.
rewrite FSuccSimpl1; simpl in |- *; auto with arith.
intros H'1 H'2.
replace p with (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q).
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto with real.
cut (Fexp (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q) = Fexp p);
 [ intros Eq0 | idtac ].
apply floatEq; auto.
apply sym_equal; apply Zeq_Zs; auto.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with arith.
rewrite FshiftCorrect; auto.
replace (Zsucc (Fnum p)) with (Fnum (Fshift radix 1 (FSucc p))); auto.
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with arith.
repeat rewrite FshiftCorrect; auto.
rewrite FSuccSimpl1; simpl in |- *; auto with arith.
unfold Fshift in |- *; simpl in |- *.
rewrite FSuccSimpl1; simpl in |- *; auto with arith.
rewrite inj_abs; auto with zarith.
unfold Fshift in |- *; simpl in |- *.
rewrite FSuccSimpl1; simpl in |- *; auto with arith.
rewrite Z.mul_1_r.
rewrite H'0.
unfold pPred in |- *; rewrite <- Zsucc_pred.
rewrite (PosNormMin radix) with (precision := precision); auto with zarith;
 apply Zmult_comm.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; auto with zarith.
generalize (Z_eq_bool_correct (Fnum p) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum p) (- nNormMin radix precision)); 
 intros H'1.
generalize (Z_eq_bool_correct (Fexp p) (- dExp b));
 case (Z_eq_bool (Fexp p) (- dExp b)); intros H'2.
pattern p at 1 in |- *; replace p with (Float (Fnum p) (Fexp p)).
rewrite H'1; rewrite H'2.
rewrite FSuccSimpl3; auto with arith.
intros H'3 H'4.
replace p with (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q).
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto with real.
cut (Fexp (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q) = Fexp p);
 [ intros Eq0 | idtac ].
apply floatEq; auto.
apply sym_equal; apply Zeq_Zs; auto.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with arith.
rewrite FshiftCorrect; auto.
replace (Zsucc (Fnum p)) with (Fnum (FSucc p)); auto.
pattern p at 2 in |- *; replace p with (Float (Fnum p) (Fexp p)).
rewrite H'1; rewrite H'2.
rewrite FSuccSimpl3; auto with arith.
rewrite <- H'2.
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with arith.
rewrite FshiftCorrect; auto.
rewrite H'2; auto.
case p; simpl in |- *; auto.
pattern p at 1 in |- *; replace p with (Float (Fnum p) (Fexp p)).
rewrite H'1; rewrite H'2.
rewrite FSuccSimpl3; auto with arith.
case p; simpl in |- *; auto.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; auto with zarith.
case p; simpl in |- *; auto.
rewrite FSuccSimpl2; auto with arith.
intros H'3 H'4.
unfold FtoRradix in |- *; rewrite <- FshiftCorrect with (n := 1) (x := p);
 auto.
replace (Fshift radix 1 p) with
 (Fshift radix (S (Zabs_nat (Fexp q - Fexp p))) q).
repeat rewrite FshiftCorrect; auto with real.
cut
 (Fexp (Fshift radix (S (Zabs_nat (Fexp q - Fexp p))) q) =
  Fexp (Fshift radix 1 p)); [ intros Eq0 | idtac ].
apply floatEq; auto.
apply sym_equal; apply Zeq_Zs; auto.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with arith.
repeat rewrite FshiftCorrect; auto.
replace (Zsucc (Fnum (Fshift radix 1 p))) with (Fnum (FSucc p)); auto.
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with arith.
repeat rewrite FshiftCorrect; auto.
rewrite FSuccSimpl2; auto with arith.
rewrite FSuccSimpl2; auto with arith.
rewrite FSuccSimpl2; auto with arith.
unfold Fshift in |- *; simpl in |- *.
rewrite Z.mul_1_r; auto.
unfold pPred in |- *;
 rewrite (PosNormMin radix) with (precision := precision); 
 auto with zarith; rewrite H'1.
rewrite Zopp_mult_distr_l_reverse.
rewrite (Zmult_comm radix).
apply Zopp_Zpred_Zs.
unfold Fshift in |- *; simpl in |- *.
replace (Zpos (P_of_succ_nat (Zabs_nat (Fexp q - Fexp p))))
 with (Zsucc (Fexp q - Fexp p)).
unfold Zsucc, Zpred in |- *; ring.
rewrite <- (inj_abs (Fexp q - Fexp p)); auto with zarith.
rewrite <- inj_S; simpl in |- *; auto.
rewrite inj_abs; auto with zarith.
rewrite FSuccSimpl4; auto.
intros H'2 H'3.
replace p with (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q).
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto with real.
cut (Fexp (Fshift radix (Zabs_nat (Fexp q - Fexp p)) q) = Fexp p);
 [ intros Eq0 | idtac ].
apply floatEq; auto.
apply sym_equal; apply Zeq_Zs; auto.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with arith.
rewrite FshiftCorrect; auto.
replace (Zsucc (Fnum p)) with (Fnum (FSucc p)); auto.
rewrite FSuccSimpl4; auto.
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with arith.
repeat rewrite FshiftCorrect; auto.
rewrite FSuccSimpl4; auto.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; auto with zarith.
Qed.
 
Definition FNSucc x := FSucc (Fnormalize radix b precision x).
 
Theorem FNSuccCanonic :
 forall a : float, Fbounded b a -> Fcanonic radix b (FNSucc a).
intros a H'; unfold FNSucc in |- *.
apply FSuccCanonic; auto with float.
Qed.
 
Theorem FNSuccLt : forall a : float, (a < FNSucc a)%R.
intros a; unfold FNSucc in |- *.
unfold FtoRradix in |- *;
 rewrite <- (FnormalizeCorrect _ radixMoreThanOne b precision a).
apply FSuccLt; auto.
Qed.
 
Theorem FNSuccProp :
 forall x y : float,
 Fbounded b x -> Fbounded b y -> (x < y)%R -> (FNSucc x <= y)%R.
intros x y H' H'0 H'1; unfold FNSucc in |- *.
replace (FtoRradix y) with (FtoRradix (Fnormalize radix b precision y)).
apply FSuccProp; auto with float.
unfold FtoRradix in |- *; repeat rewrite FnormalizeCorrect; auto.
unfold FtoRradix in |- *; repeat rewrite FnormalizeCorrect; auto.
Qed.
 
Theorem FNSuccEq :
 forall p q : float,
 Fbounded b p -> Fbounded b q -> p = q :>R -> FNSucc p = FNSucc q.
intros p q H' H'0 H'1; unfold FNSucc in |- *.
replace (Fnormalize radix b precision p) with
 (Fnormalize radix b precision q); auto.
apply FcanonicUnique with (radix := radix) (b := b) (precision := precision);
 auto with float.
repeat rewrite FnormalizeCorrect; auto.
Qed.
End suc.
Hint Resolve FSuccNormPos FBoundedSuc FSuccSubnormal FSuccNegCanonic
  FSuccCanonic FSuccLt FSuccPropPos R0RltRleSucc FSuccPropNeg FSuccProp
  FNSuccCanonic FNSuccLt: float.
Section suc1.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionNotZero : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem nNormMimLtvNum : (nNormMin radix precision < pPred (vNum b))%Z.
unfold pPred in |- *;
 rewrite PosNormMin with (radix := radix) (precision := precision);
 auto with zarith.
apply Zlt_le_trans with (Zpred (2 * nNormMin radix precision)).
replace (Zpred (2 * nNormMin radix precision)) with
 (Zpred (nNormMin radix precision) + nNormMin radix precision)%Z;
 [ idtac | unfold Zpred in |- *; ring ].
pattern (nNormMin radix precision) at 1 in |- *;
 replace (nNormMin radix precision) with (0 + nNormMin radix precision)%Z;
 [ idtac | ring ].
apply Zplus_lt_compat_r; auto.
apply Zlt_succ_pred.
replace (Zsucc 0) with (Z_of_nat 1); [ idtac | simpl in |- *; auto ].
rewrite <- (Zpower_nat_O radix); unfold nNormMin in |- *.
apply Zpower_nat_monotone_lt. assumption. now apply lt_pred.
apply Zle_Zpred_Zpred. apply Zle_Zmult_comp_r; auto with zarith.
apply Z.lt_le_incl; apply nNormPos; auto with zarith.
Qed.
 
Theorem FSucFSucMid :
 forall p : float,
 Fnum (FSucc b radix precision p) <> nNormMin radix precision ->
 Fnum (FSucc b radix precision p) <> (- nNormMin radix precision)%Z ->
 Fminus radix (FSucc b radix precision (FSucc b radix precision p))
   (FSucc b radix precision p) = Fminus radix (FSucc b radix precision p) p
 :>R.
intros p.
generalize (Z_eq_bool_correct (Fnum p) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum p) (- nNormMin radix precision)); 
 intros H'1.
generalize (Z_eq_bool_correct (Fexp p) (- dExp b));
 case (Z_eq_bool (Fexp p) (- dExp b)); intros H'2.
rewrite FSuccDiff2 with (2 := H'1); auto with arith.
replace p with (Float (Fnum p) (Fexp p)).
repeat (rewrite H'1; rewrite H'2).
rewrite FSuccSimpl3; auto with arith.
rewrite FSuccDiff1 with (2 := pGivesBound); auto with arith.
simpl in |- *; auto with zarith.
apply floatEq; auto.
unfold FtoRradix in |- *; rewrite FSuccDiff3 with (x := p) (3 := pGivesBound);
 auto with arith.
rewrite FSuccSimpl2; auto with arith.
rewrite FSuccDiff1; simpl in |- *; auto with arith.
apply Zlt_not_eq; auto.
apply Zlt_Zopp; auto.
apply nNormMimLtvNum; auto.
unfold FtoRradix in |- *; rewrite FSuccDiff1 with (x := p); simpl in |- *;
 auto with arith.
generalize (Z_eq_bool_correct (Fnum p) (pPred (vNum b)));
 case (Z_eq_bool (Fnum p) (pPred (vNum b))); intros H'2.
rewrite FSuccSimpl1; simpl in |- *; auto with arith.
intros H'; case H'; auto.
rewrite FSuccSimpl4; simpl in |- *; auto with arith.
intros H' H'0.
rewrite FSuccDiff1; simpl in |- *; auto with arith.
Qed.
 
Theorem FNSuccFNSuccMid :
 forall p : float,
 Fbounded b p ->
 Fnum (FNSucc b radix precision p) <> nNormMin radix precision ->
 Fnum (FNSucc b radix precision p) <> (- nNormMin radix precision)%Z ->
 Fminus radix (FNSucc b radix precision (FNSucc b radix precision p))
   (FNSucc b radix precision p) = Fminus radix (FNSucc b radix precision p) p
 :>R.
intros p Fb; unfold FNSucc in |- *.
intros H' H'0.
rewrite
 FcanonicFnormalizeEq
                     with
                     (p := 
                       FSucc b radix precision
                         (Fnormalize radix b precision p));
 auto with float arith.
rewrite FSucFSucMid; auto.
unfold FtoRradix in |- *; repeat rewrite Fminus_correct;
 auto with float arith.
rewrite FnormalizeCorrect; auto.
apply Zlt_trans with 1%Z; auto with zarith.
apply Zlt_trans with 1%Z; auto with zarith.
Qed.

End suc1.
Hint Resolve nNormMimLtvNum: float.
