(****************************************************************************
                                                                             
          IEEE754  :  MSBProp                                                     
                                                                             
          Laurent Thery, Sylvie Boldo                                                      
                                                                             
  ******************************************************************************)
Require Export MSB.
Section MSBProp.
Variable b : Fbound.
Variable precision : nat.
Variable radix : Z.
 
Let FtoRradix := FtoR radix.
Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO : (0 < radix)%Z :=
  Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Theorem boundOnePrecision :
 forall a : float,
 Fbounded b a -> (Rabs a < Float 1%nat (precision + Fexp a))%R.
intros a H.
replace (FtoRradix (Float 1%nat (precision + Fexp a))) with
 (FtoRradix (Fshift radix precision (Float 1%nat (precision + Fexp a))));
 [ idtac | apply (FshiftCorrect radix); auto ].
unfold Fshift, FtoRradix, FtoR in |- *; simpl in |- *.
rewrite <- pGivesBound.
replace (precision + Fexp a - precision)%Z with (Fexp a); [ idtac | ring ].
rewrite Rabs_mult; rewrite (fun x y => Rabs_pos_eq (powerRZ x y));
 auto with real zarith.
apply Rlt_monotony_exp; auto with float real zarith.
rewrite Faux.Rabsolu_Zabs; auto with float real zarith.
Qed.
 
Theorem boundNormalMult :
 forall x y : float,
 Fnormal radix b x ->
 Fbounded b y ->
 (Rabs y * Float 1%nat (Fexp x) < radix * (Rabs x * Float 1%nat (Fexp y)))%R.
intros x y H H0.
apply
 Rlt_le_trans
  with (Float (Zpos (vNum b)) (Fexp y) * Float 1%nat (Fexp x))%R.
apply Rmult_lt_compat_r.
unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *.
replace (1 * powerRZ radix (Fexp x))%R with (powerRZ radix (Fexp x));
 [ idtac | ring ].
apply powerRZ_lt; auto with real arith.
unfold FtoRradix in |- *; apply MaxFloat; auto.
replace (Float (Zpos (vNum b)) (Fexp y) * Float 1%nat (Fexp x))%R with
 (Zpos (vNum b) * Float 1%nat (Fexp x) * Float 1%nat (Fexp y))%R.
replace (radix * (Rabs x * Float 1%nat (Fexp y)))%R with
 (radix * Rabs x * Float 1%nat (Fexp y))%R; [ idtac | ring ].
apply Rmult_le_compat_r.
unfold FtoRradix in |- *; unfold FtoR in |- *; simpl in |- *.
replace (1 * powerRZ radix (Fexp y))%R with (powerRZ radix (Fexp y));
 [ idtac | ring ].
apply powerRZ_le; auto with real arith.
replace (Zpos (vNum b) * Float 1%nat (Fexp x))%R with
 (FtoRradix (Float (Zpos (vNum b)) (Fexp x))).
rewrite <- (Fabs_correct radix); auto with real zarith.
unfold Fabs, FtoRradix, FtoR in |- *.
rewrite <- Rmult_assoc.
apply Rle_monotone_exp; auto with real arith.
rewrite <- Rmult_IZR; apply Rle_IZR; simpl in |- *.
rewrite <- (Zabs_eq radix); auto with zarith; rewrite <- Zabs_Zmult;
 auto with float.
case H; simpl in |- *; auto.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
unfold FtoRradix, FtoR in |- *; simpl in |- *; ring.
Qed.
End MSBProp.