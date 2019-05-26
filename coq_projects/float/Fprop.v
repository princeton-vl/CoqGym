(****************************************************************************
                                                                             
          IEEE754  :  Fprop                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Fbound.
Section Fprop.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Variable b : Fbound.
 
Theorem SterbenzAux :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (y <= x)%R -> (x <= 2%nat * y)%R -> Fbounded b (Fminus radix x y).
intros x y H' H'0 H'1 H'2.
cut (0 <= Fminus radix x y)%R; [ intros Rle1 | idtac ].
cut (Fminus radix x y <= y)%R; [ intros Rle2 | idtac ].
case (Zle_or_lt (Fexp x) (Fexp y)); intros Zle1.
repeat split.
apply Zle_lt_trans with (Zabs (Fnum x)); auto with float.
change (Fnum (Fabs (Fminus radix x y)) <= Fnum (Fabs x))%Z in |- *.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with arith.
repeat rewrite Fabs_correct.
repeat rewrite Rabs_pos_eq; auto.
apply Rle_trans with (2 := H'1); auto.
apply Rle_trans with (2 := H'1); auto.
apply Rle_trans with (2 := Rle2); auto.
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
unfold Fminus in |- *; simpl in |- *; apply Zmin_le1; auto.
unfold Fminus in |- *; simpl in |- *; rewrite Zmin_le1; auto with float.
repeat split.
apply Zle_lt_trans with (Zabs (Fnum y)); auto with float.
change (Fnum (Fabs (Fminus radix x y)) <= Fnum (Fabs y))%Z in |- *.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with arith.
repeat rewrite Fabs_correct.
repeat rewrite Rabs_pos_eq; auto.
apply Rle_trans with (2 := Rle2); auto.
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
unfold Fminus in |- *; simpl in |- *; apply Zmin_le2; auto with zarith.
unfold Fminus in |- *; simpl in |- *; rewrite Zmin_le2;
 auto with float zarith.
rewrite (Fminus_correct radix); auto with arith; fold FtoRradix in |- *.
apply Rplus_le_reg_l with (r := FtoRradix y); auto.
replace (y + (x - y))%R with (FtoRradix x); [ idtac | ring ].
replace (y + y)%R with (2%nat * y)%R; [ auto | simpl in |- *; ring ].
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
rewrite (Fminus_correct radix); auto with arith; fold FtoRradix in |- *.
apply Rplus_le_reg_l with (r := FtoRradix y); auto.
replace (y + (x - y))%R with (FtoRradix x); [ idtac | ring ].
replace (y + 0)%R with (FtoRradix y); [ auto | simpl in |- *; ring ].
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
Qed.
 
Theorem Sterbenz :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (/ 2%nat * y <= x)%R -> (x <= 2%nat * y)%R -> Fbounded b (Fminus radix x y).
intros x y H' H'0 H'1 H'2.
cut (y <= 2%nat * x)%R; [ intros Le1 | idtac ].
case (Rle_or_lt x y); intros Le2; auto.
apply oppBoundedInv; auto.
rewrite Fopp_Fminus.
apply SterbenzAux; auto with real.
apply SterbenzAux; auto with real.
apply Rmult_le_reg_l with (r := (/ 2%nat)%R).
apply Rinv_0_lt_compat; auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real.
rewrite Rmult_1_l; auto.
Qed.
 
Theorem BminusSameExpAux :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (0 <= y)%R -> (y <= x)%R -> Fexp x = Fexp y -> Fbounded b (Fminus radix x y).
intros x y H' H'0 H'1 H'2 H'3.
cut (0 < radix)%Z; [ intros Z1 | idtac ].
rewrite minusSameExp; auto.
repeat split; simpl in |- *; auto with float.
apply Zle_lt_trans with (Zabs (Fnum x)); auto with float zarith.
change (Fnum (Fabs (Float (Fnum x - Fnum y) (Fexp x))) <= Fnum (Fabs x))%Z
 in |- *.
apply Rle_Fexp_eq_Zle with (radix := radix); auto with zarith.
rewrite <- (minusSameExp radix); auto.
repeat rewrite (Fabs_correct radix); try rewrite Fminus_correct;
 auto with zarith.
repeat rewrite Rabs_pos_eq; auto with real.
apply Rle_trans with (x - 0)%R; auto with real.
unfold Rminus in |- *; auto with real.
apply Rle_trans with (FtoRradix y); auto with real.
replace 0%R with (x - x)%R; auto with real.
unfold Rminus in |- *; auto with real.
apply Zlt_trans with (2 := radixMoreThanOne); auto with zarith.
Qed.
 
Theorem BminusSameExp :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (0 <= x)%R -> (0 <= y)%R -> Fexp x = Fexp y -> Fbounded b (Fminus radix x y).
intros x y H' H'0 H'1 H'2 H'3.
case (Rle_or_lt x y); intros Le2; auto.
apply oppBoundedInv; auto.
rewrite Fopp_Fminus.
apply BminusSameExpAux; auto.
apply BminusSameExpAux; auto with real.
Qed.
 
Theorem BminusSameExpNeg :
 forall x y : float,
 Fbounded b x ->
 Fbounded b y ->
 (x <= 0)%R -> (y <= 0)%R -> Fexp x = Fexp y -> Fbounded b (Fminus radix x y).
intros x y H' H'0 H'1 H'2 H'3.
apply oppBoundedInv; auto.
rewrite Fopp_Fminus_dist.
apply BminusSameExp; auto with float.
unfold FtoRradix in |- *; rewrite Fopp_correct.
replace 0%R with (-0)%R; auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct.
replace 0%R with (-0)%R; auto with real.
Qed.
End Fprop.
Hint Resolve Sterbenz BminusSameExp BminusSameExpNeg: float.