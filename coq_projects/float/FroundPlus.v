(****************************************************************************
                                                                             
          IEEE754  :  FroundPlus                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Finduct.
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
 
Theorem plusExpMin :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 exists s : float,
   Fbounded b s /\ s = pq :>R /\ (Zmin (Fexp p) (Fexp q) <= Fexp s)%Z.
intros P H' p q pq H'0.
case
 (RoundedModeRep b radix precision)
  with (p := Fplus radix p q) (q := pq) (P := P); auto with float arith.
rewrite Fplus_correct; auto with float arith.
simpl in |- *; intros x H'1.
case
 (eqExpLess _ radixMoreThanOne b)
  with (p := pq) (q := Float x (Fexp (Fplus radix p q))); 
 auto.
apply (RoundedModeBounded b radix) with (P := P) (r := (p + q)%R); auto.
simpl in |- *; intros x0 H'2; elim H'2; intros H'3 H'4; elim H'4;
 intros H'5 H'6; clear H'4 H'2.
exists x0; split; [ idtac | split ]; auto.
unfold FtoRradix in |- *; rewrite H'5; auto.
apply le_IZR; auto.
Qed.
 
Theorem plusExpUpperBound :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 Fbounded b p ->
 Fbounded b q ->
 exists r : float,
   Fbounded b r /\ r = pq :>R /\ (Fexp r <= Zsucc (Zmax (Fexp p) (Fexp q)))%Z.
intros P H' p q pq H'0 H'1 H'2.
replace (Zsucc (Zmax (Fexp p) (Fexp q))) with
 (Fexp (Float (pPred (vNum b)) (Zsucc (Zmax (Fexp p) (Fexp q)))));
 [ idtac | simpl in |- *; auto ].
unfold FtoRradix in |- *; apply eqExpMax; auto.
apply RoundedModeBounded with (radix := radix) (P := P) (r := (p + q)%R);
 auto with float arith.
unfold pPred in |- *; apply maxFbounded; auto.
apply Zle_trans with (Fexp p); auto with float.
apply Zle_trans with (Zsucc (Fexp p)); auto with float zarith.
replace
 (FtoR radix (Float (pPred (vNum b)) (Zsucc (Zmax (Fexp p) (Fexp q))))) with
 (radix * Float (pPred (vNum b)) (Zmax (Fexp p) (Fexp q)))%R.
rewrite Fabs_correct; auto with zarith.
unfold FtoRradix in |- *;
 apply
  RoundedModeMultAbs
   with (b := b) (precision := precision) (P := P) (r := (p + q)%R); 
 auto.
unfold pPred in |- *; apply maxFbounded; auto.
apply Zle_trans with (Fexp p); auto with float zarith.
apply Rle_trans with (Rabs p + Rabs q)%R.
apply Rabs_triang; auto.
apply
 Rle_trans
  with
    (2%nat * FtoR radix (Float (pPred (vNum b)) (Zmax (Fexp p) (Fexp q))))%R;
 auto.
cut (forall r : R, (2%nat * r)%R = (r + r)%R);
 [ intros tmp; rewrite tmp; clear tmp | intros; simpl in |- *; ring ].
apply Rplus_le_compat; auto.
rewrite <- (Fabs_correct radix); auto with arith; apply maxMax1; auto;
 apply ZmaxLe1.
rewrite <- (Fabs_correct radix); auto with arith; apply maxMax1; auto;
 apply ZmaxLe2.
apply Rmult_le_compat; auto with real arith.
replace 0%R with (INR 0); auto with real arith.
apply LeFnumZERO; simpl in |- *; auto; replace 0%Z with (Z_of_nat 0);
 auto with zarith.
unfold pPred in |- *; apply Zle_Zpred; auto with zarith.
rewrite INR_IZR_INZ; apply Rle_IZR; simpl in |- *; auto with zarith.
cut (1 < radix)%Z; auto with zarith;intros.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; ring.
Qed.
 
Theorem plusExpBound :
 forall P,
 RoundedModeP b radix P ->
 forall p q pq : float,
 P (p + q)%R pq ->
 Fbounded b p ->
 Fbounded b q ->
 exists r : float,
   Fbounded b r /\
   r = pq :>R /\
   (Zmin (Fexp p) (Fexp q) <= Fexp r)%Z /\
   (Fexp r <= Zsucc (Zmax (Fexp p) (Fexp q)))%Z.
intros P H' p q pq H'0 H'1 H'2.
case (plusExpMin P H' _ _ _ H'0).
intros r' H'3; elim H'3; intros H'4 H'5; elim H'5; intros H'6 H'7;
 clear H'5 H'3.
case (Zle_or_lt (Fexp r') (Zsucc (Zmax (Fexp p) (Fexp q)))); intros Zl1.
exists r'; repeat (split; auto).
case (plusExpUpperBound P H' _ _ _ H'0); auto.
intros r'' H'3; elim H'3; intros H'5 H'8; elim H'8; intros H'9 H'10;
 clear H'8 H'3.
exists
 (Fshift radix (Zabs_nat (Fexp r' - Zsucc (Zmax (Fexp p) (Fexp q)))) r');
 split.
apply FboundedShiftLess with (n := Zabs_nat (Fexp r' - Fexp r'')); auto.
apply ZleLe; auto.
repeat rewrite <- Zabs_absolu.
repeat rewrite Zabs_eq; auto with zarith.
rewrite FshiftCorrectInv; auto.
apply trans_eq with (FtoRradix pq); auto.
apply Zle_trans with (1 := H'10); auto with zarith.
split.
unfold FtoRradix in |- *; rewrite FshiftCorrect; auto.
split.
simpl in |- *.
repeat rewrite inj_abs; auto with zarith arith.
apply Zle_trans with (Zmax (Fexp p) (Fexp q)); auto with zarith.
apply Zmin_Zmax; auto.
simpl in |- *.
repeat rewrite inj_abs; auto with zarith arith.
Qed.
 
Theorem minusRoundRep :
 forall P,
 RoundedModeP b radix P ->
 forall p q qmp qmmp : float,
 (0 <= p)%R ->
 (p <= q)%R ->
 P (q - p)%R qmp ->
 Fbounded b p ->
 Fbounded b q -> exists r : float, Fbounded b r /\ r = (q - qmp)%R :>R.
intros P H' p q qmp H'0 H'1 H'2 H'3 H'4 H'5.
case (Rle_or_lt (/ 2%nat * q) p); intros Rle1.
exists p; split; auto.
replace (FtoRradix qmp) with (FtoRradix (Fminus radix q p)).
rewrite (Fminus_correct radix); auto with arith; unfold FtoRradix in |- *;
 ring.
apply (RoundedModeProjectorIdemEq b radix precision) with (P := P); auto.
rewrite <- Fopp_Fminus.
apply oppBounded; auto.
apply Sterbenz; auto.
apply Rle_trans with (FtoRradix q); auto with real.
apply Rledouble; auto.
apply Rle_trans with (FtoRradix p); auto with real.
cut (CompatibleP b radix P);
 [ intros Cp | apply RoundedModeP_inv2 with (1 := H'); auto ].
apply (Cp (q - p)%R (Fminus radix q p) qmp); auto.
rewrite (Fminus_correct radix); auto with arith.
apply RoundedModeBounded with (radix := radix) (P := P) (r := (q - p)%R);
 auto; auto.
exists (Fminus radix q qmp); split.
rewrite <- Fopp_Fminus.
apply oppBounded; auto.
apply Sterbenz; auto.
apply RoundedModeBounded with (radix := radix) (P := P) (r := (q - p)%R);
 auto; auto.
case MaxEx with (r := (/ 2%nat * FtoR radix q)%R) (3 := pGivesBound);
 auto with arith.
intros max H'6.
apply Rle_trans with (FtoRradix max);
 [ apply isMax_inv1 with (1 := H'6); auto | idtac ].
apply (RleBoundRoundl b radix precision) with (P := P) (r := (q - p)%R); auto;
 fold FtoRradix in |- *.
case H'6; auto.
case MinEx with (r := (/ 2%nat * FtoR radix q)%R) (3 := pGivesBound);
 auto with arith.
intros min H'7.
replace (FtoRradix max) with (q - min)%R.
apply Rplus_le_reg_l with (r := (- q)%R).
cut (forall p q : R, (- p + (p - q))%R = (- q)%R);
 [ intros tmp; repeat rewrite tmp; clear tmp | intros; ring ].
apply Ropp_le_contravar.
case H'7.
intros H'8 H'9; elim H'9; intros H'10 H'11; apply H'11; clear H'9; auto.
apply Rlt_le; auto.
unfold FtoRradix in |- *;
 rewrite (div2IsBetween b radix precision) with (5 := H'7) (6 := H'6); 
 auto.
ring.
apply Rle_trans with (FtoRradix q); auto with real.
apply (RleBoundRoundr b radix precision) with (P := P) (r := (q - p)%R); auto;
 fold FtoRradix in |- *.
apply Rplus_le_reg_l with (r := (- q)%R).
cut (forall p q : R, (- p + (p - q))%R = (- q)%R);
 [ intros tmp; repeat rewrite tmp; clear tmp | intros; ring ].
replace (- q + q)%R with (-0)%R; [ auto with real | ring ].
apply Rle_trans with (FtoRradix q); auto with real.
apply Rledouble; auto.
apply Rle_trans with (FtoRradix p); auto with real.
apply (Fminus_correct radix); auto with arith.
Qed.
 
Theorem radixRangeBoundExp :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q ->
 (0 <= p)%R ->
 (p < q)%R -> (q < radix * p)%R -> Fexp p = Fexp q \/ Zsucc (Fexp p) = Fexp q.
intros p q H' H'0 H'1 H'2 H'3.
case (FcanonicLtPos _ radixMoreThanOne b precision) with (p := p) (q := q);
 auto with arith.
2: intros H'4; elim H'4; intros H'5 H'6; clear H'4; auto.
intros H'4; right.
Casec H'; intros H'.
case
 (FcanonicLtPos _ radixMoreThanOne b precision)
  with (p := q) (q := Float (Fnum p) (Zsucc (Fexp p))); 
 auto with arith.
left.
case H'; intros H1 H2.
repeat split; simpl in |- *; auto with float.
apply Zle_trans with (Fexp p); auto with float zarith.
apply Rle_trans with (FtoRradix p); auto; apply Rlt_le; auto.
unfold FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; auto.
rewrite <- Rmult_assoc;
 rewrite (fun (x : R) (y : Z) => Rmult_comm x y); 
 rewrite Rmult_assoc; auto.
simpl in |- *; intros; apply Zle_antisym; auto with zarith.
simpl in |- *; auto.
intros H'5; elim H'5; intros H'6 H'7; auto.
case
 (FcanonicLtPos _ radixMoreThanOne b precision)
  with (p := q) (q := Float (nNormMin radix precision) (Zsucc (Fexp p)));
 auto with arith.
left; repeat split; simpl in |- *.
rewrite Zabs_eq; auto with float zarith.
apply ZltNormMinVnum; auto with zarith.
apply Zlt_le_weak; auto with zarith.
apply nNormPos; auto with zarith.
case H'; auto with zarith float.
rewrite (PosNormMin radix b precision); auto with zarith.
apply Rle_trans with (1 := H'1); auto with real.
apply Rlt_trans with (1 := H'3).
unfold FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real arith; auto.
rewrite <- Rmult_assoc;
 rewrite (fun (x : R) (y : Z) => Rmult_comm x y); 
 rewrite Rmult_assoc; auto.
apply Rmult_lt_compat_l; auto with real arith.
replace (Fexp p) with (- dExp b)%Z.
change (p < firstNormalPos radix b precision)%R in |- *.
apply (FsubnormalLtFirstNormalPos radix); auto with arith.
case H'; intros Z1 (Z2, Z3); auto.
auto with real zarith.
simpl in |- *; auto.
intros H; apply Zle_antisym; auto with zarith.
intros H'5; elim H'5; intros H'6 H'7; rewrite H'6; clear H'5; auto.
Qed.
 
Theorem ExactMinusIntervalAux :
 forall P,
 RoundedModeP b radix P ->
 forall p q : float,
 (0 < p)%R ->
 (2%nat * p < q)%R ->
 Fcanonic radix b p ->
 Fcanonic radix b q ->
 (exists r : float, Fbounded b r /\ r = (q - p)%R :>R) ->
 forall r : float,
 Fcanonic radix b r ->
 (2%nat * p < r)%R ->
 (r <= q)%R -> exists r' : float, Fbounded b r' /\ r' = (r - p)%R :>R.
intros P H' p q H'0 H'1 H'2 H'3 H'4 r H'5 H'6 H'7.
cut (0 <= p)%R; [ intros Rle0 | apply Rlt_le; auto ].
cut (0 <= r)%R; [ intros Rle1 | apply Rle_trans with (2%nat * p)%R; auto ].
2: apply Rle_trans with (FtoRradix p); auto with float arith.
2: apply Rledouble; auto.
2: apply Rlt_le; auto.
generalize H'6; clear H'6; pattern r in |- *;
 apply (FinductNeg b radix precision) with (p := q); 
 auto with arith.
apply Rle_trans with (FtoRradix r); auto.
intros q0 H'6 H'8 H'9 H'10 H'11.
elim H'10;
 [ intros r' E; elim E; intros H'13 H'14; clear E H'10 | clear H'10 ]; 
 auto.
2: apply Rlt_trans with (1 := H'11); auto; apply (FPredLt b radix precision);
    auto with arith.
cut (0 <= Fnormalize radix b precision r')%R; [ intros Rle2 | idtac ].
2: rewrite (FnormalizeCorrect radix); auto with arith.
2: unfold FtoRradix in H'14; rewrite H'14.
2: apply Rplus_le_reg_l with (r := FtoR radix p).
2: replace (FtoR radix p + 0)%R with (FtoR radix p); [ idtac | ring ].
2: replace (FtoR radix p + (FtoR radix q0 - FtoR radix p))%R with
    (FtoR radix q0); [ idtac | ring ].
2: apply Rle_trans with (2%nat * p)%R; auto.
2: apply Rledouble; auto with real arith.
2: apply Rlt_le; apply Rlt_trans with (1 := H'11); auto with float.
2: apply (FPredLt b radix precision); auto with arith.
cut (Fnormalize radix b precision r' < q0)%R; [ intros Rle3 | idtac ].
2: rewrite (FnormalizeCorrect radix); auto with arith.
2: unfold FtoRradix in H'14; rewrite H'14.
2: apply Rplus_lt_reg_l with (r := (- q0)%R).
2: replace (- q0 + (FtoR radix q0 - FtoR radix p))%R with (- p)%R;
    [ idtac | unfold FtoRradix in |- *; ring; ring ].
2: replace (- q0 + q0)%R with (-0)%R; [ auto with real | ring ].
case radixRangeBoundExp with (p := Fnormalize radix b precision r') (q := q0);
 auto with float arith; fold FtoRradix in |- *.
rewrite (FnormalizeCorrect radix); auto with arith.
apply Rlt_le_trans with (2%nat * r')%R; auto.
rewrite H'14.
rewrite Rmult_minus_distr_l.
pattern (FtoRradix q0) at 1 in |- *;
 (replace (FtoRradix q0) with (2%nat * q0 - q0)%R;
   [ idtac | simpl in |- *; ring ]).
unfold Rminus in |- *; apply Rplus_lt_compat_l; apply Ropp_lt_contravar.
apply Rlt_trans with (1 := H'11).
apply (FPredLt b radix precision); auto with arith.
apply Rmult_le_compat_r; auto with real arith.
unfold FtoRradix in Rle2; rewrite (FnormalizeCorrect radix) in Rle2;
 auto with arith.
rewrite INR_IZR_INZ; cut (2 <= radix)%Z; auto with real zarith.
cut (1 < radix)%Z; auto with zarith.
intros H'10.
case
 (FcanonicLtPos _ radixMoreThanOne b precision)
  with (p := Fnormalize radix b precision r') (q := q0); 
 auto with arith.
apply FnormalizeCanonic; auto with arith.
intros; Contradict H'10; auto with zarith.
intros H'12; elim H'12; intros H'15 H'16; clear H'12.
exists
 (Float (Zpred (Fnum (Fnormalize radix b precision r')))
    (Fexp (Fnormalize radix b precision r'))).
split.
cut (Fbounded b (Fnormalize radix b precision r')); [ intros Fb0 | idtac ].
repeat split; simpl in |- *; auto with float.
case Rle2; intros Z1.
apply Zle_lt_trans with (Zabs (Fnum (Fnormalize radix b precision r')));
 auto with float zarith.
repeat rewrite Zabs_eq; auto with zarith.
apply (LeR0Fnum radix); auto with zarith.
apply Zle_Zpred; apply (LtR0Fnum radix); auto with zarith.
replace (Fnum (Fnormalize radix b precision r')) with 0%Z; simpl in |- *;
 auto with zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
apply sym_equal; change (is_Fzero (Fnormalize radix b precision r')) in |- *;
 apply (is_Fzero_rep2 radix); auto with zarith.
apply FcanonicBound with (radix := radix); auto.
apply FnormalizeCanonic; auto with arith.
replace
 (Float (Zpred (Fnum (Fnormalize radix b precision r')))
    (Fexp (Fnormalize radix b precision r'))) with
 (Fminus radix (Fnormalize radix b precision r')
    (Fminus radix q0 (FPred b radix precision q0))).
repeat rewrite (Fopp_correct radix); repeat rewrite (Fminus_correct radix);
 auto with arith.
rewrite (FnormalizeCorrect radix); auto with arith.
unfold FtoRradix in H'14; rewrite H'14.
unfold FtoRradix in |- *; ring; ring.
replace (FPred b radix precision q0) with (Float (Zpred (Fnum q0)) (Fexp q0));
 auto.
unfold Fminus, Fopp, Fplus in |- *; simpl in |- *.
repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse; simpl in |- *;
 auto.
rewrite H.
repeat rewrite Zmin_n_n; repeat rewrite <- Zminus_diag_reverse; simpl in |- *;
 auto.
repeat rewrite Zmult_1_r.
apply floatEq; simpl in |- *; auto; unfold Zpred in |- *; ring.
case (Z_eq_dec (Fnum q0) (nNormMin radix precision)); intros Zeq2.
case (Z_eq_dec (Fexp q0) (- dExp b)); intros Zeq1.
rewrite Zeq1; rewrite Zeq2; rewrite <- (FPredSimpl3 b radix); auto with arith;
 rewrite <- Zeq1; rewrite <- Zeq2; auto.
Contradict H'16.
apply Zle_not_lt.
rewrite Zeq2.
rewrite <- (Zabs_eq (Fnum (Fnormalize radix b precision r')));
 auto with zarith.
apply pNormal_absolu_min with (b := b); auto with arith.
cut (Fcanonic radix b (Fnormalize radix b precision r'));
 [ intros Ca1; case Ca1; auto | auto with float arith ].
intros H'12; case Zeq1; rewrite <- H.
case H'12; auto.
intros Hbis H0; case H0; auto.
apply (LeR0Fnum radix); auto.
rewrite FPredSimpl4; auto.
Contradict H'16; rewrite H'16.
apply Zle_not_lt.
unfold pPred in |- *; rewrite Zopp_Zpred_Zs; apply Zlt_le_succ.
apply Zlt_Zabs_inv1.
cut (Fbounded b (Fnormalize radix b precision r'));
 [ auto with float | idtac ].
apply (FcanonicBound radix b); auto with float arith.
intros H'10.
case (Z_eq_dec (Fnum q0) (nNormMin radix precision)); intros Zeq2.
exists
 (Float (Zpred (Fnum (Fnormalize radix b precision r')))
    (Fexp (Fnormalize radix b precision r'))).
cut (Fbounded b (Fnormalize radix b precision r')); [ intros Fb1 | idtac ].
repeat split; simpl in |- *; auto with float.
case Rle2; intros Z1.
apply Zlt_trans with (Zabs (Fnum (Fnormalize radix b precision r'))).
repeat rewrite Zabs_eq; auto with zarith.
apply (LeR0Fnum radix); auto.
apply Zle_Zpred; apply (LtR0Fnum radix); auto.
case Fb1; auto.
replace (Fnum (Fnormalize radix b precision r')) with 0%Z.
simpl in |- *; apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
apply sym_equal; change (is_Fzero (Fnormalize radix b precision r')) in |- *;
 apply (is_Fzero_rep2 radix); auto with zarith.
rewrite FPredSimpl2; auto with zarith.
rewrite <- H'10.
cut (forall z : Z, Zpred (Zsucc z) = z);
 [ intros tmp; rewrite tmp; clear tmp
 | intros; unfold Zsucc, Zpred in |- *; ring ].
unfold FtoRradix, FtoR in |- *; simpl in |- *.
cut (forall x : Z, Zpred x = (x - 1%nat)%Z);
 [ intros tmp; rewrite tmp; clear tmp
 | intros; unfold Zpred in |- *; simpl in |- *; ring ].
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite <- Z_R_minus; auto.
rewrite (fun x y => Rmult_comm (x - y)); rewrite Rmult_minus_distr_l;
 repeat rewrite (fun x y => Rmult_comm (powerRZ x y)).
replace
 (Fnum (Fnormalize radix b precision r') *
  powerRZ radix (Fexp (Fnormalize radix b precision r')))%R with
 (FtoRradix (Fnormalize radix b precision r')).
rewrite (FnormalizeCorrect radix); auto.
unfold FtoRradix in H'14; rewrite H'14.
unfold FtoR in |- *; simpl in |- *.
pattern (Fexp q0) at 1 in |- *; rewrite <- H'10.
rewrite Zeq2; rewrite powerRZ_Zs; auto with real zarith.
rewrite <- Rmult_assoc.
replace (nNormMin radix precision * radix)%R with (powerRZ radix precision).
unfold pPred, nNormMin, Zpred in |- *; rewrite pGivesBound.
rewrite plus_IZR; repeat rewrite Zpower_nat_Z_powerRZ; simpl in |- *; try ring.
rewrite <- Zpower_nat_Z_powerRZ; auto with zarith; rewrite <- Rmult_IZR;
 rewrite Zmult_comm; rewrite <- (PosNormMin radix b precision);
 auto with real zarith.
auto.
red in |- *; intros H'12;
 absurd (- dExp b <= Fexp (Fnormalize radix b precision r'))%Z;
 auto with float.
apply Zlt_not_le.
rewrite <- H'12; rewrite <- H'10; unfold Zsucc in |- *;
 auto with float zarith.
apply (FcanonicBound radix b); auto with arith.
apply FnormalizeCanonic; auto with arith.
exists
 (Float (Fnum (Fnormalize radix b precision r') - radix)
    (Fexp (Fnormalize radix b precision r'))).
cut (Fbounded b (Fnormalize radix b precision r')); [ intros Fb1 | idtac ].
repeat split; simpl in |- *; auto with float.
case (Zle_or_lt (Fnum (Fnormalize radix b precision r')) radix); intros Z1.
apply Zle_lt_trans with radix.
rewrite Zabs_eq_opp; auto with zarith.
cut (0 <= Fnum (Fnormalize radix b precision r'))%Z; auto with zarith.
apply (LeR0Fnum radix); auto.
rewrite <- (Zpower_nat_1 radix); rewrite pGivesBound; auto with zarith.
apply Zle_lt_trans with (Zabs (Fnum (Fnormalize radix b precision r'))).
repeat rewrite Zabs_eq; auto with zarith.
case Fb1; auto.
rewrite FPredSimpl4; auto with arith.
rewrite <- H'10.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
cut (forall x : Z, Zpred x = (x - 1%nat)%Z);
 [ intros tmp; rewrite tmp; clear tmp
 | intros; unfold Zpred in |- *; simpl in |- *; ring ].
repeat rewrite <- Z_R_minus; auto.
repeat rewrite (fun x y => Rmult_comm (x - y));
 repeat rewrite Rmult_minus_distr_l;
 repeat rewrite (fun x y => Rmult_comm (powerRZ x y)).
replace
 (Fnum (Fnormalize radix b precision r') *
  powerRZ radix (Fexp (Fnormalize radix b precision r')))%R with
 (FtoRradix (Fnormalize radix b precision r')).
rewrite (FnormalizeCorrect radix); auto.
unfold FtoRradix in H'14; rewrite H'14.
unfold FtoR in |- *; simpl in |- *.
rewrite <- H'10.
repeat rewrite powerRZ_Zs; auto with real arith.
ring.
auto with real zarith.
unfold FtoR in |- *; simpl in |- *; auto.
red in |- *; intros H'12; absurd (0 <= Fnum q0)%Z; auto.
apply Zlt_not_le.
rewrite H'12.
replace 0%Z with (- 0%nat)%Z; [ apply Zlt_Zopp | simpl in |- *; auto ].
unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *; auto with zarith.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
apply (LeR0Fnum radix); auto.
apply Rlt_le; auto.
apply (FcanonicBound radix b); auto with arith.
apply FnormalizeCanonic; auto with arith.
Qed.
 
Theorem ExactMinusIntervalAux1 :
 forall P,
 RoundedModeP b radix P ->
 forall p q : float,
 (0 <= p)%R ->
 (p <= q)%R ->
 Fcanonic radix b p ->
 Fcanonic radix b q ->
 (exists r : float, Fbounded b r /\ r = (q - p)%R :>R) ->
 forall r : float,
 Fcanonic radix b r ->
 (p <= r)%R ->
 (r <= q)%R -> exists r' : float, Fbounded b r' /\ r' = (r - p)%R :>R.
intros P H' p q H'0 H'1 H'2 H'3 H'4 r H'5 H'6 H'7.
Casec H'0; intros H'0.
case (Rle_or_lt q (2%nat * p)); intros Rl1.
exists (Fminus radix r p); split; auto.
rewrite <- Fopp_Fminus.
apply oppBounded.
apply Sterbenz; auto.
apply (FcanonicBound radix b); auto with arith.
apply (FcanonicBound radix b); auto with arith.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real arith;
 rewrite Rmult_1_l; auto.
apply Rle_trans with (1 := H'7); auto.
apply Rle_trans with (1 := H'6); auto.
apply Rledouble; auto.
apply Rle_trans with (2 := H'6); apply Rlt_le; auto.
rewrite (Fminus_correct radix); auto with arith.
case (Rle_or_lt r (2%nat * p)); intros Rl2.
exists (Fminus radix r p); split; auto.
rewrite <- Fopp_Fminus.
apply oppBounded.
apply Sterbenz; auto.
apply (FcanonicBound radix b); auto with arith.
apply (FcanonicBound radix b); auto with arith.
apply Rmult_le_reg_l with (r := INR 2); auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_r; auto with real arith;
 rewrite Rmult_1_l; auto.
apply Rle_trans with (1 := H'6); auto.
apply Rledouble; auto.
apply Rle_trans with (2 := H'6); apply Rlt_le; auto.
rewrite (Fminus_correct radix); auto with arith.
apply ExactMinusIntervalAux with (P := P) (q := q); auto.
exists r; split; auto.
apply (FcanonicBound radix b); auto with arith.
rewrite <- H'0; ring.
Qed.
 
Theorem ExactMinusInterval :
 forall P,
 RoundedModeP b radix P ->
 forall p q : float,
 (0 <= p)%R ->
 (p <= q)%R ->
 Fbounded b p ->
 Fbounded b q ->
 (exists r : float, Fbounded b r /\ r = (q - p)%R :>R) ->
 forall r : float,
 Fbounded b r ->
 (p <= r)%R ->
 (r <= q)%R -> exists r' : float, Fbounded b r' /\ r' = (r - p)%R :>R.
intros P H' p q H'0 H'1 H'2 H'3 H'4 r H'5 H'6 H'7.
replace (FtoRradix r) with (FtoRradix (Fnormalize radix b precision r));
 [ idtac | apply (FnormalizeCorrect radix) ]; auto.
replace (FtoRradix p) with (FtoRradix (Fnormalize radix b precision p));
 [ idtac | apply (FnormalizeCorrect radix) ]; auto.
apply
 ExactMinusIntervalAux1 with (P := P) (q := Fnormalize radix b precision q);
 auto; try repeat rewrite (FnormalizeCorrect radix); 
 auto; apply FnormalizeCanonic; auto with arith.
Qed.
(* Properties concerning LSB MSB *)
 
Theorem MSBroundLSB :
 forall P : R -> float -> Prop,
 RoundedModeP b radix P ->
 forall f1 f2 : float,
 P f1 f2 ->
 ~ is_Fzero (Fminus radix f1 f2) ->
 (MSB radix (Fminus radix f1 f2) < LSB radix f2)%Z.
intros P H' f1 f2 H'0 HZ.
apply (oneExp_Zlt radix); auto.
apply Rlt_le_trans with (Fulp b radix precision f2).
apply Rle_lt_trans with (FtoRradix (Fabs (Fminus radix f1 f2))).
unfold FtoRradix in |- *; apply MSB_le_abs; auto.
unfold FtoRradix in |- *; rewrite Fabs_correct; auto with arith;
 rewrite Fminus_correct; auto with arith.
apply RoundedModeUlp with (4 := H'); auto.
apply FUlp_Le_LSigB; auto.
apply RoundedModeBounded with (1 := H') (2 := H'0); auto.
Qed.
 
Theorem LSBMinus :
 forall p q : float,
 ~ is_Fzero (Fminus radix p q) ->
 (Zmin (LSB radix p) (LSB radix q) <= LSB radix (Fminus radix p q))%Z.
intros p q H'1.
elim (LSB_rep_min radix) with (p := p); auto; intros z E.
elim (LSB_rep_min radix) with (p := q); auto; intros z0 E0.
replace (LSB radix (Fminus radix p q)) with
 (LSB radix (Fminus radix (Float z (LSB radix p)) (Float z0 (LSB radix q)))).
replace (Zmin (LSB radix p) (LSB radix q)) with
 (Fexp (Fminus radix (Float z (LSB radix p)) (Float z0 (LSB radix q))));
 [ idtac | simpl in |- *; auto ].
apply Fexp_le_LSB; auto.
apply sym_equal; apply LSB_comp; auto.
repeat rewrite Fminus_correct; auto with arith.
unfold FtoRradix in E; unfold FtoRradix in E0; rewrite E; rewrite E0; auto.
Qed.
 
Theorem LSBPlus :
 forall p q : float,
 ~ is_Fzero (Fplus radix p q) ->
 (Zmin (LSB radix p) (LSB radix q) <= LSB radix (Fplus radix p q))%Z.
intros p q H'.
elim (LSB_rep_min _ radixMoreThanOne p); intros z E.
elim (LSB_rep_min _ radixMoreThanOne q); intros z0 E0.
replace (LSB radix (Fplus radix p q)) with
 (LSB radix (Fplus radix (Float z (LSB radix p)) (Float z0 (LSB radix q)))).
replace (Zmin (LSB radix p) (LSB radix q)) with
 (Fexp (Fplus radix (Float z (LSB radix p)) (Float z0 (LSB radix q))));
 [ idtac | simpl in |- *; auto ].
apply Fexp_le_LSB; auto.
apply sym_equal; apply LSB_comp; auto.
repeat rewrite Fplus_correct; auto with arith.
unfold FtoRradix in E; unfold FtoRradix in E0; rewrite E; rewrite E0; auto.
Qed.
 
End FRoundP.
