(****************************************************************************
                                                                             
          IEEE754  :  Fop                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Fcomp.
Section operations.
Variable radix : Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixNotZero : (0 < radix)%Z.
 
Definition Fplus (x y : float) :=
  Float
    (Fnum x * Zpower_nat radix (Zabs_nat (Fexp x - Zmin (Fexp x) (Fexp y))) +
     Fnum y * Zpower_nat radix (Zabs_nat (Fexp y - Zmin (Fexp x) (Fexp y))))
    (Zmin (Fexp x) (Fexp y)).
 
Theorem Fplus_correct : forall x y : float, Fplus x y = (x + y)%R :>R.
intros x y; unfold Fplus, Fshift, FtoRradix, FtoR in |- *; simpl in |- *.
rewrite plus_IZR.
rewrite Rmult_comm; rewrite Rmult_plus_distr_l; auto.
repeat rewrite Rmult_IZR.
repeat rewrite (Rmult_comm (Fnum x)); repeat rewrite (Rmult_comm (Fnum y)).
repeat rewrite Zpower_nat_Z_powerRZ; auto.
repeat rewrite <- Rmult_assoc.
repeat rewrite <- powerRZ_add; auto with real zarith arith.
repeat rewrite inj_abs; auto with real zarith.
repeat rewrite Zplus_minus; auto.
Qed.
 
Definition Fopp (x : float) := Float (- Fnum x) (Fexp x).
 
Theorem Fopp_correct : forall x : float, Fopp x = (- x)%R :>R.
unfold FtoRradix, FtoR, Fopp in |- *; simpl in |- *.
intros x.
rewrite Ropp_Ropp_IZR; auto with real.
Qed.
 
Theorem Fopp_Fopp : forall p : float, Fopp (Fopp p) = p.
intros p; case p; unfold Fopp in |- *; simpl in |- *; auto.
intros; rewrite Zopp_involutive; auto.
Qed.
 
Theorem Fzero_opp : forall f : float, ~ is_Fzero f -> ~ is_Fzero (Fopp f).
intros f; case f; intros n e; case n; unfold is_Fzero in |- *; simpl in |- *;
 auto with zarith; intros; red in |- *; intros; discriminate.
Qed.
 
Theorem Fdigit_opp : forall x : float, Fdigit radix (Fopp x) = Fdigit radix x.
intros x; unfold Fopp, Fdigit in |- *; simpl in |- *.
rewrite <- (digit_abs radix (- Fnum x)).
rewrite <- (digit_abs radix (Fnum x)).
case (Fnum x); simpl in |- *; auto.
Qed.
 
Definition Fabs (x : float) := Float (Zabs (Fnum x)) (Fexp x).
 
Theorem Fabs_correct1 :
 forall x : float, (0 <= FtoR radix x)%R -> Fabs x = x :>R.
intros x; case x; unfold FtoRradix, FtoR in |- *; simpl in |- *.
intros Fnum1 Fexp1 H'.
repeat rewrite <- (Rmult_comm (powerRZ radix Fexp1)); apply Rmult_eq_compat_l;
 auto.
cut (0 <= Fnum1)%Z.
unfold Zabs, Zle in |- *.
case Fnum1; simpl in |- *; auto.
intros p H'0; case H'0; auto.
apply Znot_gt_le; auto.
Contradict H'.
apply Rgt_not_le; auto.
rewrite Rmult_comm.
replace 0%R with (powerRZ radix Fexp1 * 0)%R; auto with real.
red in |- *; apply Rmult_lt_compat_l; auto with real zarith.
Qed.
 
Theorem Fabs_correct2 :
 forall x : float, (FtoR radix x <= 0)%R -> Fabs x = (- x)%R :>R.
intros x; case x; unfold FtoRradix, FtoR in |- *; simpl in |- *.
intros Fnum1 Fexp1 H'.
rewrite <- Ropp_mult_distr_l_reverse;
 repeat rewrite <- (Rmult_comm (powerRZ radix Fexp1));
 apply Rmult_eq_compat_l; auto.
cut (Fnum1 <= 0)%Z.
unfold Zabs, Zle in |- *.
case Fnum1; unfold IZR; auto with real.
intros p H'0; case H'0; auto.
apply Znot_gt_le.
Contradict H'.
apply Rgt_not_le; auto.
rewrite Rmult_comm.
replace 0%R with (powerRZ radix Fexp1 * 0)%R; auto with real.
red in |- *; apply Rmult_lt_compat_l; auto with real arith.
replace 0%R with (IZR 0); auto with real zarith arith.
Qed.
 
Theorem Fabs_correct : forall x : float, Fabs x = Rabs x :>R.
intros x; unfold Rabs in |- *.
case (Rcase_abs x); intros H1.
unfold FtoRradix in |- *; apply Fabs_correct2; auto with arith.
apply Rlt_le; auto.
unfold FtoRradix in |- *; apply Fabs_correct1; auto with arith.
apply Rge_le; auto.
Qed.
 
Theorem RleFexpFabs :
 forall p : float, p <> 0%R :>R -> (Float 1%nat (Fexp p) <= Fabs p)%R.
intros p H'.
unfold FtoRradix, FtoR, Fabs in |- *; simpl in |- *.
apply Rmult_le_compat_r; auto with real arith.
rewrite Zabs_absolu.
replace 1%R with (INR 1); auto with real.
repeat rewrite <- INR_IZR_INZ; apply Rle_INR; auto.
cut (Zabs_nat (Fnum p) <> 0); auto with zarith.
Contradict H'.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
replace (Fnum p) with 0%Z; try (simpl;ring).
generalize H'; case (Fnum p); simpl in |- *; auto with zarith arith;
 intros p0 H'3; Contradict H'3; auto with zarith arith.
Qed.
 
Theorem Fabs_Fzero : forall x : float, ~ is_Fzero x -> ~ is_Fzero (Fabs x).
intros x; case x; unfold is_Fzero in |- *; simpl in |- *.
intros n m; case n; simpl in |- *; auto with zarith; intros; red in |- *;
 discriminate.
Qed.
Hint Resolve Fabs_Fzero: float.
 
Theorem Fdigit_abs : forall x : float, Fdigit radix (Fabs x) = Fdigit radix x.
intros x; unfold Fabs, Fdigit in |- *; simpl in |- *.
case (Fnum x); auto.
Qed.
 
Definition Fminus (x y : float) := Fplus x (Fopp y).
 
Theorem Fminus_correct : forall x y : float, Fminus x y = (x - y)%R :>R.
intros x y; unfold Fminus in |- *.
rewrite Fplus_correct.
rewrite Fopp_correct; auto.
Qed.
 
Theorem Fopp_Fminus : forall p q : float, Fopp (Fminus p q) = Fminus q p.
intros p q; case p; case q; unfold Fopp, Fminus, Fplus in |- *; simpl in |- *;
 auto.
intros; apply floatEq; simpl in |- *; repeat rewrite (Zmin_sym Fexp0 Fexp);
 repeat rewrite Zopp_mult_distr_l_reverse; auto with zarith.
Qed.
 
Theorem Fopp_Fminus_dist :
 forall p q : float, Fopp (Fminus p q) = Fminus (Fopp p) (Fopp q).
intros p q; case p; case q; unfold Fopp, Fminus, Fplus in |- *; simpl in |- *;
 auto.
intros; apply floatEq; simpl in |- *; repeat rewrite (Zmin_sym Fexp0 Fexp);
 repeat rewrite Zopp_mult_distr_l_reverse; auto with zarith.
Qed.
 
Theorem minusSameExp :
 forall x y : float,
 Fexp x = Fexp y -> Fminus x y = Float (Fnum x - Fnum y) (Fexp x).
intros x y; case x; case y; unfold Fminus, Fplus, Fopp in |- *; simpl in |- *.
intros Fnum1 Fexp1 Fnum2 Fexp2 H'; rewrite <- H'.
repeat rewrite Zmin_n_n.
apply floatEq; simpl in |- *; auto.
replace (Zabs_nat (Fexp2 - Fexp2)) with 0; auto with zarith arith.
replace (Zpower_nat radix 0) with (Z_of_nat 1); simpl in |- *;
 auto with zarith arith.
replace (Fexp2 - Fexp2)%Z with 0%Z; simpl in |- *; auto with zarith arith.
Qed.
 
Definition Fmult (x y : float) := Float (Fnum x * Fnum y) (Fexp x + Fexp y).
 
Definition Fmult_correct : forall x y : float, Fmult x y = (x * y)%R :>R.
intros x y; unfold FtoRradix, FtoR, Fmult in |- *; simpl in |- *; auto.
rewrite powerRZ_add; auto with real zarith.
repeat rewrite Rmult_IZR.
repeat rewrite Rmult_assoc.
repeat rewrite (Rmult_comm (Fnum y)).
repeat rewrite <- Rmult_assoc.
repeat rewrite Zmult_assoc_reverse; auto.
Qed.
 
Theorem oneZplus :
 forall x y : Z,
 Float 1%nat (x + y) = Fmult (Float 1%nat x) (Float 1%nat y).
intros x y; unfold Fmult in |- *; auto.
Qed.
End operations.
Hint Resolve Fabs_Fzero: float.
Hint Resolve Fzero_opp: float.