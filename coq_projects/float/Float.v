(****************************************************************************
                                                                             
          IEEE754  :  Float                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  ******************************************************
   Module Float.v 				   	
   Inspired by the Diadic of Patrick Loiseleur
  *******************************************************)
Require Export Omega.
Require Export Compare.
Require Export Rpow.
Section definitions.
Variable radix : Z.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
(* The type float represents the set of numbers who can be written:  	
   x = n*b^p with  n and p in Z. (pdic numbers)				
   n = Fnum and p = Fexp 						*)
 
Record float : Set := Float {Fnum : Z; Fexp : Z}.
 
Theorem floatEq :
 forall p q : float, Fnum p = Fnum q -> Fexp p = Fexp q -> p = q.
intros p q; case p; case q; simpl in |- *; intros;
 apply (f_equal2 (A1:=Z) (A2:=Z)); auto.
Qed.
 
Theorem floatDec : forall x y : float, {x = y} + {x <> y}.
intros x y; case x; case y; intros Fnum2 Fexp2 Fnum1 Fexp1.
case (Z_eq_dec Fnum1 Fnum2); intros H1.
case (Z_eq_dec Fexp1 Fexp2); intros H2.
left; apply floatEq; auto.
right; red in |- *; intros H'; Contradict H2; inversion H'; auto.
right; red in |- *; intros H'; Contradict H1; inversion H'; auto.
Qed.
 
Definition Fzero (x : Z) := Float 0 x.
 
Definition is_Fzero (x : float) := Fnum x = 0%Z.
 
Theorem is_FzeroP : forall x : float, is_Fzero x \/ ~ is_Fzero x.
unfold is_Fzero in |- *; intro; CaseEq (Fnum x); intros;
 (right; discriminate) || (left; auto).
Qed.
Coercion IZR : Z >-> R.
Coercion INR : nat >-> R.
Coercion Z_of_nat : nat >-> Z.
 
Definition FtoR (x : float) := (Fnum x * powerRZ (IZR radix) (Fexp x))%R.
 
Local Coercion FtoR : float >-> R.
 
Theorem FzeroisReallyZero : forall z : Z, Fzero z = 0%R :>R.
intros z; unfold FtoR in |- *; simpl in |- *; auto with real.
Qed.
 
Theorem is_Fzero_rep1 : forall x : float, is_Fzero x -> x = 0%R :>R.
intros x H; unfold FtoR in |- *.
red in H; rewrite H; simpl in |- *; auto with real.
Qed.
 
Theorem LtFnumZERO : forall x : float, (0 < Fnum x)%Z -> (0 < x)%R.
intros x; case x; unfold FtoR in |- *; simpl in |- *.
intros Fnum1 Fexp1 H'; replace 0%R with (Fnum1 * 0)%R;
 [ apply Rmult_lt_compat_l | ring ]; auto with real zarith.
Qed.
 
Theorem is_Fzero_rep2 : forall x : float, x = 0%R :>R -> is_Fzero x.
intros x H'.
case (Rmult_integral _ _ H'); simpl in |- *; auto.
case x; simpl in |- *.
intros Fnum1 Fexp1 H'0; red in |- *; simpl in |- *; auto with real zarith.
apply eq_IZR_R0; auto.
intros H'0; Contradict H'0; apply powerRZ_NOR; auto with real zarith.
Qed.
 
Theorem NisFzeroComp :
 forall x y : float, ~ is_Fzero x -> x = y :>R -> ~ is_Fzero y.
intros x y H' H'0; Contradict H'.
apply is_Fzero_rep2; auto.
rewrite H'0.
apply is_Fzero_rep1; auto.
Qed.
(* Some inegalities that will be helpful *)
 
Theorem Rlt_monotony_exp :
 forall (x y : R) (z : Z),
 (x < y)%R -> (x * powerRZ radix z < y * powerRZ radix z)%R.
intros x y z H'; apply Rmult_lt_compat_r; auto with real zarith.
Qed.
 
Theorem Rle_monotone_exp :
 forall (x y : R) (z : Z),
 (x <= y)%R -> (x * powerRZ radix z <= y * powerRZ radix z)%R.
intros x y z H'; apply Rmult_le_compat_r; auto with real zarith.
Qed.
 
Theorem Rlt_monotony_contra_exp :
 forall (x y : R) (z : Z),
 (x * powerRZ radix z < y * powerRZ radix z)%R -> (x < y)%R.
intros x y z H'; apply Rmult_lt_reg_l with (r := powerRZ radix z);
 auto with real zarith.
repeat rewrite (Rmult_comm (powerRZ radix z)); auto.
Qed.
 
Theorem Rle_monotony_contra_exp :
 forall (x y : R) (z : Z),
 (x * powerRZ radix z <= y * powerRZ radix z)%R -> (x <= y)%R.
intros x y z H'; apply Rmult_le_reg_l with (r := powerRZ radix z);
 auto with real zarith.
repeat rewrite (Rmult_comm (powerRZ radix z)); auto.
Qed.
 
Theorem FtoREqInv1 :
 forall p q : float, ~ is_Fzero p -> p = q :>R -> Fnum p = Fnum q -> p = q.
intros p q H' H'0 H'1.
apply floatEq; auto.
unfold FtoR in H'0.
apply Rpow_eq_inv with (r := IZR radix); auto 6 with real zarith.
apply Rlt_dichotomy_converse; right; red in |- *.
unfold Rabs in |- *; case (Rcase_abs radix).
intros H'2; Contradict H'2; apply Rle_not_lt; apply Ropp_le_cancel;
 auto with real.
intros H'2; replace 1%R with (IZR 1); auto with real zarith.
apply Rmult_eq_reg_l with (r := IZR (Fnum p)); auto with real.
pattern (Fnum p) at 2 in |- *; rewrite H'1; auto.
Qed.
 
Theorem FtoREqInv2 :
 forall p q : float, p = q :>R -> Fexp p = Fexp q -> p = q.
intros p q H' H'0.
apply floatEq; auto.
apply eq_IZR; auto.
apply Rmult_eq_reg_l with (r := powerRZ radix (Fexp p));
 auto with real zarith.
repeat rewrite (Rmult_comm (powerRZ radix (Fexp p)));
 pattern (Fexp p) at 2 in |- *; rewrite H'0; auto with real zarith.
Qed.
 
Theorem Rlt_Float_Zlt :
 forall p q r : Z, (Float p r < Float q r)%R -> (p < q)%Z.
intros p q r H'.
apply lt_IZR.
apply Rlt_monotony_contra_exp with (z := r); auto with real.
Qed.
 
Theorem Rle_Float_Zle :
 forall p q r : Z, (Float p r <= Float q r)%R -> (p <= q)%Z.
intros p q r H'.
apply le_IZR.
apply Rle_monotony_contra_exp with (z := r); auto with real.
Qed.
(* Properties for floats with 1 as mantissa *)
 
Theorem oneExp_le :
 forall x y : Z, (x <= y)%Z -> (Float 1%nat x <= Float 1%nat y)%R.
intros x y H'; unfold FtoR in |- *; simpl in |- *.
repeat rewrite Rmult_1_l; auto with real zarith.
apply Rle_powerRZ; try replace 1%R with (IZR 1); auto with real zarith zarith.
Qed.
 
Theorem oneExp_lt :
 forall x y : Z, (x < y)%Z -> (Float 1%nat x < Float 1%nat y)%R.
intros x y H'; unfold FtoR in |- *; simpl in |- *.
repeat rewrite Rmult_1_l; auto with real zarith.
Qed.
 
Theorem oneExp_Zlt :
 forall x y : Z, (Float 1%nat x < Float 1%nat y)%R -> (x < y)%Z.
intros x y H'; case (Zle_or_lt y x); auto; intros ZH; Contradict H'.
apply Rle_not_lt; apply oneExp_le; auto.
Qed.
 
Theorem oneExp_Zle :
 forall x y : Z, (Float 1%nat x <= Float 1%nat y)%R -> (x <= y)%Z.
intros x y H'; case (Zle_or_lt x y); auto; intros ZH; Contradict H'.
apply Rgt_not_le; red in |- *; apply oneExp_lt; auto.
Qed.
 
Definition Fdigit (p : float) := digit radix (Fnum p).
 
Definition Fshift (n : nat) (x : float) :=
  Float (Fnum x * Zpower_nat radix n) (Fexp x - n).
 
Theorem sameExpEq : forall p q : float, p = q :>R -> Fexp p = Fexp q -> p = q.
intros p q; case p; case q; unfold FtoR in |- *; simpl in |- *.
intros Fnum1 Fexp1 Fnum2 Fexp2 H' H'0; rewrite H'0; rewrite H'0 in H'.
cut (Fnum1 = Fnum2).
intros H'1; rewrite <- H'1; auto.
apply eq_IZR; auto.
apply Rmult_eq_reg_l with (r := powerRZ radix Fexp1);
 repeat rewrite (Rmult_comm (powerRZ radix Fexp1)); 
 auto.
apply Rlt_dichotomy_converse; right; auto with real.
red in |- *; auto with real.
Qed.
 
Theorem FshiftFdigit :
 forall (n : nat) (x : float),
 ~ is_Fzero x -> Fdigit (Fshift n x) = Fdigit x + n.
intros n x; case x; unfold Fshift, Fdigit, is_Fzero in |- *; simpl in |- *.
intros p1 p2 H; apply digitAdd; auto.
Qed.
 
Theorem FshiftCorrect : forall (n : nat) (x : float), Fshift n x = x :>R.
intros n x; unfold FtoR in |- *; simpl in |- *.
rewrite Rmult_IZR.
rewrite Zpower_nat_Z_powerRZ; auto.
repeat rewrite Rmult_assoc.
rewrite <- powerRZ_add; auto with real zarith.
rewrite Zplus_minus; auto.
Qed.
 
Theorem FshiftCorrectInv :
 forall x y : float,
 x = y :>R ->
 (Fexp x <= Fexp y)%Z -> Fshift (Zabs_nat (Fexp y - Fexp x)) y = x.
intros x y H' H'0; try apply sameExpEq; auto.
apply trans_eq with (y := FtoR y); auto.
apply FshiftCorrect.
generalize H' H'0; case x; case y; simpl in |- *; clear H' H'0 x y.
intros Fnum1 Fexp1 Fnum2 Fexp2 H' H'0; rewrite inj_abs; auto with zarith.
Qed.
 
Theorem FshiftO : forall x : float, Fshift 0 x = x.
intros x; unfold Fshift in |- *; apply floatEq; simpl in |- *.
replace (Zpower_nat radix 0) with 1%Z; auto with zarith.
simpl in |- *; auto with zarith.
Qed.
 
Theorem FshiftCorrectSym :
 forall x y : float,
 x = y :>R -> exists n : nat, (exists m : nat, Fshift n x = Fshift m y).
intros x y H'.
case (Z_le_gt_dec (Fexp x) (Fexp y)); intros H'1.
exists 0; exists (Zabs_nat (Fexp y - Fexp x)).
rewrite FshiftO.
apply sym_equal.
apply FshiftCorrectInv; auto.
exists (Zabs_nat (Fexp x - Fexp y)); exists 0.
rewrite FshiftO.
apply FshiftCorrectInv; auto with zarith.
Qed.
 
Theorem FshiftAdd :
 forall (n m : nat) (p : float), Fshift (n + m) p = Fshift n (Fshift m p).
intros n m p; case p; unfold Fshift in |- *; simpl in |- *.
intros Fnum1 Fexp1; apply floatEq; simpl in |- *; auto with zarith.
rewrite Zpower_nat_is_exp; auto with zarith.
rewrite (Zmult_comm (Zpower_nat radix n)); auto with zarith.
rewrite <- (Zminus_plus_simpl_r (Fexp1 - m) n m).
replace (Fexp1 - m + m)%Z with Fexp1; auto with zarith.
replace (Z_of_nat (n + m)) with (n + m)%Z; auto with zarith arith.
rewrite <- inj_plus; auto.
Qed.
 
Theorem ReqGivesEqwithSameExp :
 forall p q : float,
 exists r : float,
   (exists s : float, p = r :>R /\ q = s :>R /\ Fexp r = Fexp s).
intros p q; exists (Fshift (Zabs_nat (Fexp p - Zmin (Fexp p) (Fexp q))) p);
 exists (Fshift (Zabs_nat (Fexp q - Zmin (Fexp p) (Fexp q))) q); 
 repeat split; auto with real.
rewrite FshiftCorrect; auto.
rewrite FshiftCorrect; auto.
simpl in |- *.
replace (Z_of_nat (Zabs_nat (Fexp p - Zmin (Fexp p) (Fexp q)))) with
 (Fexp p - Zmin (Fexp p) (Fexp q))%Z.
replace (Z_of_nat (Zabs_nat (Fexp q - Zmin (Fexp p) (Fexp q)))) with
 (Fexp q - Zmin (Fexp p) (Fexp q))%Z.
case (Zmin_or (Fexp p) (Fexp q)); intros H'; rewrite H'; auto with zarith.
rewrite inj_abs; auto.
apply Zplus_le_reg_l with (p := Zmin (Fexp p) (Fexp q)); auto with zarith.
generalize (Zle_min_r (Fexp p) (Fexp q)); auto with zarith.
rewrite inj_abs; auto.
apply Zplus_le_reg_l with (p := Zmin (Fexp p) (Fexp q)); auto with zarith.
Qed.
 
Theorem FdigitEq :
 forall x y : float,
 ~ is_Fzero x -> x = y :>R -> Fdigit x = Fdigit y -> x = y.
intros x y H' H'0 H'1.
cut (~ is_Fzero y); [ intros NZy | idtac ].
2: red in |- *; intros H'2; case H'.
2: apply is_Fzero_rep2; rewrite H'0; apply is_Fzero_rep1; auto.
case (Zle_or_lt (Fexp x) (Fexp y)); intros Eq1.
case (Zle_lt_or_eq _ _ Eq1); clear Eq1; intros Eq1.
absurd
 (Fdigit (Fshift (Zabs_nat (Fexp y - Fexp x)) y) =
  Fdigit y + Zabs_nat (Fexp y - Fexp x)).
rewrite FshiftCorrectInv; auto.
rewrite <- H'1.
red in |- *; intros H'2.
absurd (0%Z = (Fexp y - Fexp x)%Z); auto with zarith arith.
rewrite <- (inj_abs (Fexp y - Fexp x)); auto with zarith.
apply Zlt_le_weak; auto.
apply FshiftFdigit; auto.
apply sameExpEq; auto.
absurd
 (Fdigit (Fshift (Zabs_nat (Fexp x - Fexp y)) x) =
  Fdigit x + Zabs_nat (Fexp x - Fexp y)).
rewrite FshiftCorrectInv; auto.
rewrite <- H'1.
red in |- *; intros H'2.
absurd (0%Z = (Fexp x - Fexp y)%Z); auto with zarith arith.
rewrite <- (inj_abs (Fexp x - Fexp y)); auto with zarith.
apply Zlt_le_weak; auto.
apply FshiftFdigit; auto.
Qed.
End definitions.
Hint Resolve Rlt_monotony_exp Rle_monotone_exp: real.
Hint Resolve Zlt_not_eq Zlt_not_eq_rev: zarith.