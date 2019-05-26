(****************************************************************************
                                                                             
          IEEE754  :  Fcomp                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Float.
Section comparisons.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
 
Definition Fdiff (x y : float) :=
  (Fnum x * Zpower_nat radix (Zabs_nat (Fexp x - Zmin (Fexp x) (Fexp y))) -
   Fnum y * Zpower_nat radix (Zabs_nat (Fexp y - Zmin (Fexp x) (Fexp y))))%Z.

Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Theorem Fdiff_correct :
 forall x y : float,
 (Fdiff x y * powerRZ radix (Zmin (Fexp x) (Fexp y)))%R = (x - y)%R.
intros x y; unfold Fdiff in |- *.
rewrite <- Z_R_minus.
rewrite Rmult_comm; rewrite Rmult_minus_distr_l.
repeat rewrite Rmult_IZR.
repeat rewrite Zpower_nat_Z_powerRZ; auto.
rewrite (Rmult_comm (Fnum x)); rewrite (Rmult_comm (Fnum y)).
repeat rewrite <- Rmult_assoc.
repeat rewrite <- powerRZ_add; auto with real zarith.
repeat rewrite inj_abs; auto with arith.
repeat rewrite Zplus_minus; auto.
rewrite (fun t : R => Rmult_comm t (Fnum x));
 rewrite (fun t : R => Rmult_comm t (Fnum y)); auto.
apply Zplus_le_reg_l with (p := Zmin (Fexp x) (Fexp y)); auto with arith.
rewrite Zplus_minus; rewrite Zplus_0_r; apply Zle_min_r; auto.
apply Zplus_le_reg_l with (p := Zmin (Fexp x) (Fexp y)); auto with arith.
rewrite Zplus_minus; rewrite Zplus_0_r; apply Zle_min_l; auto.
Qed.
(* Definition of  comparison functions*)
 
Definition Feq (x y : float) := x = y :>R.
 
Definition Fle (x y : float) := (x <= y)%R.
 
Definition Flt (x y : float) := (x < y)%R.
 
Definition Fge (x y : float) := (x >= y)%R.
 
Definition Fgt (x y : float) := (x > y)%R.
 
Definition Fcompare (x y : float) := (Fdiff x y ?= 0)%Z.
 
Definition Feq_bool (x y : float) :=
  match Fcompare x y with
  | Eq => true
  | _ => false
  end.
 
Theorem Feq_bool_correct_t :
 forall x y : float, Feq_bool x y = true -> Feq x y.
intros x y H'; red in |- *.
apply Rplus_eq_reg_l with (r := (- y)%R).
repeat rewrite (Rplus_comm (- y)).
rewrite Rplus_opp_r.
change ((x - y)%R = 0%R) in |- *.
rewrite <- Fdiff_correct.
apply Rmult_eq_0_compat_r; auto.
cut (Fdiff x y = 0%Z); [ intros H; rewrite H | idtac ]; auto with real.
apply Zcompare_EGAL.
generalize H'; unfold Feq_bool, Fcompare in |- *.
case (Fdiff x y ?= 0)%Z;auto; intros; discriminate.
Qed.
 
Theorem Feq_bool_correct_r :
 forall x y : float, Feq x y -> Feq_bool x y = true.
intros x y H'; cut ((x - y)%R = 0%R).
rewrite <- Fdiff_correct; intros H'1; case Rmult_integral with (1 := H'1).
intros H'0; unfold Feq_bool, Fcompare in |- *.
rewrite eq_IZR_R0 with (1 := H'0); auto.
intros H'0; Contradict H'0.
case (Zmin (Fexp x) (Fexp y)); simpl in |- *; auto with real zarith.
apply Rplus_eq_reg_l with (r := FtoR radix y); auto with real.
Qed.
 
Theorem Feq_bool_correct_f :
 forall x y : float, Feq_bool x y = false -> ~ Feq x y.
intros x y H'; Contradict H'.
rewrite Feq_bool_correct_r; auto with arith.
red in |- *; intros H'0; discriminate.
Qed.
 
Definition Flt_bool (x y : float) :=
  match Fcompare x y with
  | Lt => true
  | _ => false
  end.
 
Theorem Flt_bool_correct_t :
 forall x y : float, Flt_bool x y = true -> Flt x y.
intros x y H'; red in |- *.
apply Rplus_lt_reg_r with (r := (- y)%R).
repeat rewrite (Rplus_comm (- y)).
rewrite Rplus_opp_r.
change (x - y < 0)%R in |- *.
rewrite <- Fdiff_correct.
replace 0%R with (powerRZ radix (Zmin (Fexp x) (Fexp y)) * 0)%R;
 auto with real arith.
rewrite (Rmult_comm (Fdiff x y)).
apply Rmult_lt_compat_l; auto with real zarith.
replace 0%R with (IZR 0); auto with real arith.
apply Rlt_IZR; red in |- *.
generalize H'; unfold Flt_bool, Fcompare in |- *.
case (Fdiff x y ?= 0)%Z; auto; intros; try discriminate.
Qed.
 
Theorem Flt_bool_correct_r :
 forall x y : float, Flt x y -> Flt_bool x y = true.
intros x y H'.
cut (0 < y - x)%R; auto with arith.
2: apply Rplus_lt_reg_l with (r := FtoRradix x); rewrite Rplus_0_r;
    rewrite Rplus_minus; auto with real.
intros H'0.
cut (Fdiff x y < 0)%R; auto with arith.
intros H'1.
cut (Fdiff x y < 0)%Z; auto with zarith.
intros H'2; generalize (Zlt_compare _ _ H'2);
 unfold Flt_bool, Fcompare, Zcompare in |- *; case (Fdiff x y);
 auto with arith; intros; contradiction.
apply lt_IZR; auto with arith.
apply (Rlt_monotony_contra_exp radix) with (z := Zmin (Fexp x) (Fexp y));
 auto with arith real; rewrite Rmult_0_l.
rewrite Fdiff_correct; auto with real.
Qed.
 
Theorem Flt_bool_correct_f :
 forall x y : float, Flt_bool x y = false -> Fle y x.
intros x y H'.
case (Rtotal_order (FtoRradix y) (FtoRradix x)); auto with real.
intros H'0; red in |- *; apply Rlt_le; auto with real.
intros H'0; elim H'0; clear H'0; intros H'1.
red in |- *; rewrite H'1; auto with real.
Contradict H'; rewrite Flt_bool_correct_r; auto with real.
red in |- *; intros H'; discriminate.
Qed.
 
Definition Fle_bool (x y : float) :=
  match Fcompare x y with
  | Lt => true
  | Eq => true
  | _ => false
  end.
 
Theorem Fle_bool_correct_t :
 forall x y : float, Fle_bool x y = true -> Fle x y.
intros x y H'.
cut (Feq x y \/ Flt x y).
intros H; case H; intros H1; auto with real.
red in |- *; apply Req_le; auto with real.
red in |- *; apply Rlt_le; auto with real.
generalize H' (Feq_bool_correct_t x y) (Flt_bool_correct_t x y).
unfold Fle_bool, Feq_bool, Flt_bool in |- *; case (Fcompare x y); auto.
Qed.
 
Theorem Fle_bool_correct_r :
 forall x y : float, Fle x y -> Fle_bool x y = true.
intros x y H'.
cut (Feq x y \/ Flt x y).
intros H; case H; intros H1; auto with real.
generalize (Feq_bool_correct_r x y).
unfold Fle_bool, Feq_bool, Flt_bool in |- *; case (Fcompare x y); auto.
generalize (Flt_bool_correct_r x y);
 unfold Fle_bool, Feq_bool, Flt_bool in |- *; case (Fcompare x y);
 auto with arith.
case H'; auto with arith.
Qed.
 
Theorem Fle_bool_correct_f :
 forall x y : float, Fle_bool x y = false -> Flt y x.
intros x y H'.
case (Rtotal_order (FtoRradix y) (FtoRradix x)); auto with real.
intros H'0; elim H'0; clear H'0; intros H'1.
Contradict H'.
rewrite Fle_bool_correct_r; auto with real.
red in |- *; intros H'; discriminate.
red in |- *; rewrite H'1; auto with real.
Contradict H'.
rewrite Fle_bool_correct_r; auto with real.
red in |- *; intros H'; discriminate.
red in |- *; auto with real.
Qed.
 
Lemma Fle_Zle :
 forall n1 n2 d : Z, (n1 <= n2)%Z -> Fle (Float n1 d) (Float n2 d).
intros; unfold Fle, FtoRradix, FtoR in |- *; simpl in |- *; auto.
case Zle_lt_or_eq with (1 := H); intros H1.
apply Rlt_le; auto with real.
rewrite <- H1; auto with real.
Qed.
 
Lemma Flt_Zlt :
 forall n1 n2 d : Z, (n1 < n2)%Z -> Flt (Float n1 d) (Float n2 d).
intros; unfold Flt, FtoRradix, FtoR in |- *; simpl in |- *; auto with real.
Qed.
 
Lemma Fle_Fge : forall x y : float, Fle x y -> Fge y x.
unfold Fle, Fge in |- *; intros x y H'; auto with real.
Qed.
 
Lemma Fge_Zge :
 forall n1 n2 d : Z, (n1 >= n2)%Z -> Fge (Float n1 d) (Float n2 d).
intros n1 n2 d H'; apply Fle_Fge; auto.
apply Fle_Zle; auto.
apply Zge_le; auto.
Qed.
 
Lemma Flt_Fgt : forall x y : float, Flt x y -> Fgt y x.
unfold Flt, Fgt in |- *; intros x y H'; auto.
Qed.
 
Lemma Fgt_Zgt :
 forall n1 n2 d : Z, (n1 > n2)%Z -> Fgt (Float n1 d) (Float n2 d).
intros n1 n2 d H'; apply Flt_Fgt; auto.
apply Flt_Zlt; auto.
apply Zgt_lt; auto.
Qed.
(* Arithmetic properties on F : Fle is reflexive, transitive, antisymmetric *)
 
Lemma Fle_refl : forall x y : float, Feq x y -> Fle x y.
unfold Feq in |- *; unfold Fle in |- *; intros.
rewrite H; auto with real.
Qed.
 
Lemma Fle_trans : forall x y z : float, Fle x y -> Fle y z -> Fle x z.
unfold Fle in |- *; intros.
apply Rle_trans with (r2 := FtoR radix y); auto.
Qed.
 
Theorem Rlt_Fexp_eq_Zlt :
 forall x y : float, (x < y)%R -> Fexp x = Fexp y -> (Fnum x < Fnum y)%Z.
intros x y H' H'0.
apply lt_IZR.
apply (Rlt_monotony_contra_exp radix) with (z := Fexp x);
 auto with real arith.
pattern (Fexp x) at 2 in |- *; rewrite H'0; auto.
Qed.
 
Theorem Rle_Fexp_eq_Zle :
 forall x y : float, (x <= y)%R -> Fexp x = Fexp y -> (Fnum x <= Fnum y)%Z.
intros x y H' H'0.
apply le_IZR.
apply (Rle_monotony_contra_exp radix) with (z := Fexp x);
 auto with real arith.
pattern (Fexp x) at 2 in |- *; rewrite H'0; auto.
Qed.
 
Theorem LtR0Fnum : forall p : float, (0 < p)%R -> (0 < Fnum p)%Z.
intros p H'.
apply lt_IZR.
apply (Rlt_monotony_contra_exp radix) with (z := Fexp p);
 auto with real arith.
simpl in |- *; rewrite Rmult_0_l; auto.
Qed.
 
Theorem LeR0Fnum : forall p : float, (0 <= p)%R -> (0 <= Fnum p)%Z.
intros p H'.
apply le_IZR.
apply (Rle_monotony_contra_exp radix) with (z := Fexp p);
 auto with real arith.
simpl in |- *; rewrite Rmult_0_l; auto.
Qed.
 
Theorem LeFnumZERO : forall x : float, (0 <= Fnum x)%Z -> (0 <= x)%R.
intros x H'; unfold FtoRradix, FtoR in |- *.
replace 0%R with (0%Z * 0%Z)%R; auto 6 with real zarith.
Qed.
 
Theorem R0LtFnum : forall p : float, (p < 0)%R -> (Fnum p < 0)%Z.
intros p H'.
apply lt_IZR.
apply (Rlt_monotony_contra_exp radix) with (z := Fexp p);
 auto with real arith.
simpl in |- *; rewrite Rmult_0_l; auto.
Qed.
 
Theorem R0LeFnum : forall p : float, (p <= 0)%R -> (Fnum p <= 0)%Z.
intros p H'.
apply le_IZR.
apply (Rle_monotony_contra_exp radix) with (z := Fexp p);
 auto with real arith.
simpl in |- *; rewrite Rmult_0_l; auto.
Qed.
 
Theorem LeZEROFnum : forall x : float, (Fnum x <= 0)%Z -> (x <= 0)%R.
intros x H'; unfold FtoRradix, FtoR in |- *.
apply Ropp_le_cancel; rewrite Ropp_0; rewrite <- Ropp_mult_distr_l_reverse.
replace 0%R with (- 0%Z * 0)%R; auto 6 with real zarith.
Qed.
End comparisons.
Hint Resolve LeFnumZERO LeZEROFnum: float.