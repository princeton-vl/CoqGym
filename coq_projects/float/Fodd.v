(****************************************************************************
                                                                             
          IEEE754  :  Fodd                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Fmin.
Section FOdd.
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
(* We define the parity predicates*)
 
Definition Even (z : Z) : Prop := exists z1 : _, z = (2 * z1)%Z.
 
Definition Odd (z : Z) : Prop := exists z1 : _, z = (2 * z1 + 1)%Z.
 
Theorem OddSEven : forall n : Z, Odd n -> Even (Zsucc n).
intros n H'; case H'; intros m H'1; exists (Zsucc m).
rewrite H'1; unfold Zsucc in |- *; ring.
Qed.
 
Theorem EvenSOdd : forall n : Z, Even n -> Odd (Zsucc n).
intros n H'; case H'; intros m H'1; exists m.
rewrite H'1; unfold Zsucc in |- *; ring.
Qed.
Hint Resolve OddSEven EvenSOdd: zarith.
 
Theorem OddSEvenInv : forall n : Z, Odd (Zsucc n) -> Even n.
intros n H'; case H'; intros m H'1; exists m.
apply Zsucc_inj; rewrite H'1; (unfold Zsucc in |- *; ring).
Qed.
 
Theorem EvenSOddInv : forall n : Z, Even (Zsucc n) -> Odd n.
intros n H'; case H'; intros m H'1; exists (Zpred m).
apply Zsucc_inj; rewrite H'1; (unfold Zsucc, Zpred in |- *; ring).
Qed.
 
Theorem EvenO : Even 0.
exists 0%Z; simpl in |- *; auto.
Qed.
Hint Resolve EvenO: zarith.
 
Theorem Odd1 : Odd 1.
exists 0%Z; simpl in |- *; auto.
Qed.
Hint Resolve Odd1: zarith.
 
Theorem OddOpp : forall z : Z, Odd z -> Odd (- z).
intros z H; case H; intros z1 H1; exists (- Zsucc z1)%Z; rewrite H1.
unfold Zsucc in |- *; ring.
Qed.
 
Theorem EvenOpp : forall z : Z, Even z -> Even (- z).
intros z H; case H; intros z1 H1; exists (- z1)%Z; rewrite H1; ring.
Qed.
Hint Resolve OddOpp EvenOpp: zarith.
 
Theorem OddEvenDec : forall n : Z, {Odd n} + {Even n}.
intros z; case z; simpl in |- *; auto with zarith.
intros p; case p; simpl in |- *; auto with zarith.
intros p1; left; exists (Zpos p1); rewrite Zplus_comm;
 simpl in |- *; auto.
intros p1; right; exists (Zpos p1); simpl in |- *; auto.
change
  (forall p : positive,
   {Odd (- Zpos p)} + {Even (- Zpos p)}) 
 in |- *.
intros p; case p; auto with zarith.
intros p1; left; apply OddOpp; exists (Zpos p1);
 rewrite Zplus_comm; simpl in |- *; auto.
intros p1; right; apply EvenOpp; exists (Zpos p1); simpl in |- *; auto.
Qed.
 
Theorem OddNEven : forall n : Z, Odd n -> ~ Even n.
intros n H1; red in |- *; intros H2; case H1; case H2; intros z1 Hz1 z2 Hz2.
absurd (n = n); auto.
pattern n at 1 in |- *; rewrite Hz1; rewrite Hz2;
 repeat rewrite (fun x => Zplus_comm x 1).
case z1; case z2; simpl in |- *;
 try (intros; red in |- *; intros; discriminate).
intros p p0; case p; simpl in |- *;
 try (intros; red in |- *; intros; discriminate).
Qed.
 
Theorem EvenNOdd : forall n : Z, Even n -> ~ Odd n.
intros n H1; red in |- *; intros H2; case H1; case H2; intros z1 Hz1 z2 Hz2.
absurd (n = n); auto.
pattern n at 1 in |- *; rewrite Hz1; rewrite Hz2;
 repeat rewrite (fun x => Zplus_comm x 1).
case z1; case z2; simpl in |- *;
 try (intros; red in |- *; intros; discriminate).
intros p p0; case p0; simpl in |- *;
 try (intros; red in |- *; intros; discriminate).
Qed.
Hint Resolve OddNEven EvenNOdd: zarith.
 
Theorem EvenPlus1 : forall n m : Z, Even n -> Even m -> Even (n + m).
intros n m H H0; case H; case H0; intros z1 Hz1 z2 Hz2.
exists (z2 + z1)%Z; try rewrite Hz1; try rewrite Hz2; ring.
Qed.
 
Theorem EvenPlus2 : forall n m : Z, Odd n -> Odd m -> Even (n + m).
intros n m H H0; case H; case H0; intros z1 Hz1 z2 Hz2.
exists (z2 + z1 + 1)%Z; try rewrite Hz1; try rewrite Hz2; ring.
Qed.
 
Theorem OddPlus1 : forall n m : Z, Odd n -> Even m -> Odd (n + m).
intros n m H H0; case H; case H0; intros z1 Hz1 z2 Hz2.
exists (z2 + z1)%Z; try rewrite Hz1; try rewrite Hz2; ring.
Qed.
 
Theorem OddPlus2 : forall n m : Z, Even n -> Odd m -> Odd (n + m).
intros n m H H0; case H; case H0; intros z1 Hz1 z2 Hz2.
exists (z2 + z1)%Z; try rewrite Hz1; try rewrite Hz2; ring.
Qed.
Hint Resolve EvenPlus1 EvenPlus2 OddPlus1 OddPlus2: zarith.
 
Theorem EvenPlusInv1 :
 forall n m : Z, Even (n + m) -> Even n -> Even m.
intros n m H H0; replace m with (n + m + - n)%Z; auto with zarith.
Qed.
 
Theorem EvenPlusInv2 : forall n m : Z, Even (n + m) -> Odd n -> Odd m.
intros n m H H0; replace m with (n + m + - n)%Z; auto with zarith.
Qed.
 
Theorem OddPlusInv1 : forall n m : Z, Odd (n + m) -> Odd m -> Even n.
intros n m H H0; replace n with (n + m + - m)%Z; auto with zarith.
Qed.
 
Theorem OddPlusInv2 : forall n m : Z, Odd (n + m) -> Even m -> Odd n.
intros n m H H0; replace n with (n + m + - m)%Z; auto with zarith.
Qed.
 
Theorem EvenMult1 : forall n m : Z, Even n -> Even (n * m).
intros n m H; case H; intros z1 Hz1; exists (z1 * m)%Z; rewrite Hz1; ring.
Qed.
 
Theorem EvenMult2 : forall n m : Z, Even m -> Even (n * m).
intros n m H; case H; intros z1 Hz1; exists (z1 * n)%Z; rewrite Hz1; ring.
Qed.
Hint Resolve EvenMult1 EvenMult2: zarith.
 
Theorem OddMult : forall n m : Z, Odd n -> Odd m -> Odd (n * m).
intros n m H1 H2; case H1; case H2; intros z1 Hz1 z2 Hz2;
 exists (2 * z1 * z2 + z1 + z2)%Z; rewrite Hz1; rewrite Hz2; 
 ring.
Qed.
Hint Resolve OddMult: zarith.
 
Theorem EvenMultInv : forall n m : Z, Even (n * m) -> Odd n -> Even m.
intros n m H H0; case (OddEvenDec m); auto; intros Z1.
Contradict H; auto with zarith.
Qed.
 
Theorem OddMultInv : forall n m : Z, Odd (n * m) -> Odd n.
intros n m H; case (OddEvenDec n); auto; intros Z1.
Contradict H; auto with zarith.
Qed.
 
Theorem EvenExp :
 forall (n : Z) (m : nat), Even n -> Even (Zpower_nat n (S m)).
intros n m; elim m.
rewrite Zpower_nat_1; simpl in |- *; auto with zarith.
intros n0 H H0; replace (S (S n0)) with (1 + S n0); auto with arith.
rewrite Zpower_nat_is_exp; rewrite Zpower_nat_1; simpl in |- *;
 auto with zarith.
Qed.
 
Theorem OddExp :
 forall (n : Z) (m : nat), Odd n -> Odd (Zpower_nat n m).
intros n m; elim m; simpl in |- *. auto with zarith.
intros n0 H H0; replace (S n0) with (1 + n0); auto with arith.
auto with zarith.
Qed.
Hint Resolve OddExp EvenExp: zarith.
 
Definition Feven (p : float) := Even (Fnum p).
 
Definition Fodd (p : float) := Odd (Fnum p).
 
Theorem FevenO : forall p : float, is_Fzero p -> Feven p.
intros p H'; red in |- *; rewrite H'; simpl in |- *; auto with zarith.
Qed.
 
Theorem FevenOrFodd : forall p : float, Feven p \/ Fodd p.
intros p; case (OddEvenDec (Fnum p)); auto.
Qed.
 
Theorem FevenSucProp :
 forall p : float,
 (Fodd p -> Feven (FSucc b radix precision p)) /\
 (Feven p -> Fodd (FSucc b radix precision p)).
intros p; unfold FSucc, Fodd, Feven in |- *.
generalize (Z_eq_bool_correct (Fnum p) (pPred (vNum b)));
 case (Z_eq_bool (Fnum p) (pPred (vNum b))); intros H'1.
rewrite H'1; simpl in |- *; auto.
unfold pPred in |- *; rewrite pGivesBound; unfold nNormMin in |- *.
case (OddEvenDec radix); auto with zarith.
intros H'; split; intros H'0; auto with zarith.
apply EvenMultInv with (n := radix); auto.
pattern radix at 1 in |- *; rewrite <- Zpower_nat_1;
 rewrite <- Zpower_nat_is_exp.
replace (1 + pred precision) with precision;
 [ idtac | inversion precisionGreaterThanOne; auto ].
rewrite (Zsucc_pred (Zpower_nat radix precision)); auto with zarith.
intros H'; split; intros H'0; auto with zarith.
replace (pred precision) with (S (pred (pred precision))); auto with zarith.
Contradict H'0; apply OddNEven.
replace (Zpred (Zpower_nat radix precision)) with
 (Zpower_nat radix precision + - (1))%Z;
 [ idtac | unfold Zpred in |- *; simpl in |- *; auto ].
replace precision with (S (pred precision));
 [ auto with zarith | inversion precisionGreaterThanOne; auto ].
generalize (Z_eq_bool_correct (Fnum p) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum p) (- nNormMin radix precision)); 
 intros H'2.
generalize (Z_eq_bool_correct (Fexp p) (- dExp b));
 case (Z_eq_bool (Fexp p) (- dExp b)); intros H'3.
simpl in |- *; auto with zarith.
simpl in |- *; auto with zarith.
rewrite H'2; unfold pPred, nNormMin in |- *; rewrite pGivesBound.
case (OddEvenDec radix); auto with zarith.
intros H'; split; intros H'0; auto with zarith.
apply EvenOpp; apply OddSEvenInv; rewrite <- Zsucc_pred; auto with zarith.
Contradict H'0; replace precision with (S (pred precision));
 [ auto with zarith | inversion precisionGreaterThanOne; auto ].
intros H'; split; intros H'0; auto with zarith.
Contradict H'0; replace (pred precision) with (S (pred (pred precision)));
 [ auto with zarith | auto with zarith ].
replace precision with (S (pred precision));
 [ auto with zarith | inversion precisionGreaterThanOne; auto ].
apply OddOpp; apply EvenSOddInv; rewrite <- Zsucc_pred; auto with zarith.
simpl in |- *; auto with zarith.
Qed.
 
Theorem FoddSuc :
 forall p : float, Fodd p -> Feven (FSucc b radix precision p).
intros p H'; case (FevenSucProp p); auto.
Qed.
 
Theorem FevenSuc :
 forall p : float, Feven p -> Fodd (FSucc b radix precision p).
intros p H'; case (FevenSucProp p); auto.
Qed.
 
Theorem FevenFop : forall p : float, Feven p -> Feven (Fopp p).
intros p; unfold Feven, Fopp in |- *; simpl in |- *; auto with zarith.
Qed.
 
Theorem FoddFop : forall p : float, Fodd p -> Fodd (Fopp p).
intros p; unfold Fodd, Fopp in |- *; simpl in |- *; auto with zarith.
Qed.
 
Theorem FevenPred :
 forall p : float, Fodd p -> Feven (FPred b radix precision p).
intros p H'; rewrite FPredFopFSucc; auto with arith.
apply FevenFop; auto.
apply FoddSuc; auto.
apply FoddFop; auto with arith.
Qed.
 
Theorem FoddPred :
 forall p : float, Feven p -> Fodd (FPred b radix precision p).
intros p H'; rewrite FPredFopFSucc; auto with arith.
apply FoddFop; auto.
apply FevenSuc; auto.
apply FevenFop; auto.
Qed.
 
Definition FNodd (p : float) := Fodd (Fnormalize radix b precision p).
 
Definition FNeven (p : float) := Feven (Fnormalize radix b precision p).
 
Theorem FNoddEq :
 forall f1 f2 : float,
 Fbounded b f1 -> Fbounded b f2 -> f1 = f2 :>R -> FNodd f1 -> FNodd f2.
intros f1 f2 H' H'0 H'1 H'2; red in |- *.
rewrite
 FcanonicUnique
                with
                (3 := pGivesBound)
               (p := Fnormalize radix b precision f2)
               (q := Fnormalize radix b precision f1); 
 auto with float arith.
repeat rewrite FnormalizeCorrect; auto.
Qed.
 
Theorem FNevenEq :
 forall f1 f2 : float,
 Fbounded b f1 -> Fbounded b f2 -> f1 = f2 :>R -> FNeven f1 -> FNeven f2.
intros f1 f2 H' H'0 H'1 H'2; red in |- *.
rewrite
 FcanonicUnique
                with
                (3 := pGivesBound)
               (p := Fnormalize radix b precision f2)
               (q := Fnormalize radix b precision f1); 
 auto with float arith.
repeat rewrite FnormalizeCorrect; auto.
Qed.
 
Theorem FNevenFop : forall p : float, FNeven p -> FNeven (Fopp p).
intros p; unfold FNeven in |- *.
rewrite Fnormalize_Fopp; auto with arith.
intros; apply FevenFop; auto.
Qed.
 
Theorem FNoddFop : forall p : float, FNodd p -> FNodd (Fopp p).
intros p; unfold FNodd in |- *.
rewrite Fnormalize_Fopp; auto with arith.
intros; apply FoddFop; auto.
Qed.
 
Theorem FNoddSuc :
 forall p : float,
 Fbounded b p -> FNodd p -> FNeven (FNSucc b radix precision p).
unfold FNodd, FNeven, FNSucc in |- *.
intros p H' H'0.
rewrite FcanonicFnormalizeEq; auto with float arith.
apply FoddSuc; auto with float arith.
Qed.
 
Theorem FNevenSuc :
 forall p : float,
 Fbounded b p -> FNeven p -> FNodd (FNSucc b radix precision p).
unfold FNodd, FNeven, FNSucc in |- *.
intros p H' H'0.
rewrite FcanonicFnormalizeEq; auto with float arith.
apply FevenSuc; auto.
Qed.
 
Theorem FNevenPred :
 forall p : float,
 Fbounded b p -> FNodd p -> FNeven (FNPred b radix precision p).
unfold FNodd, FNeven, FNPred in |- *.
intros p H' H'0.
rewrite FcanonicFnormalizeEq; auto with float arith.
apply FevenPred; auto.
Qed.
 
Theorem FNoddPred :
 forall p : float,
 Fbounded b p -> FNeven p -> FNodd (FNPred b radix precision p).
unfold FNodd, FNeven, FNPred in |- *.
intros p H' H'0.
rewrite FcanonicFnormalizeEq; auto with float arith.
apply FoddPred; auto.
Qed.
 
Theorem FNevenOrFNodd : forall p : float, FNeven p \/ FNodd p.
intros p; unfold FNeven, FNodd in |- *; apply FevenOrFodd.
Qed.
 
Theorem FnOddNEven : forall n : float, FNodd n -> ~ FNeven n.
intros n H'; unfold FNeven, Feven in |- *; apply OddNEven; auto.
Qed.
 
Theorem FEvenD :
 forall p : float,
 Fbounded b p ->
 Feven p -> exists q : float, Fbounded b q /\ p = (2%nat * q)%R :>R.
intros p H H0; case H0.
intros z Hz; exists (Float z (Fexp p)); split; auto.
repeat split; simpl in |- *; auto with float.
apply Zle_lt_trans with (Zabs (Fnum p)); auto with float zarith.
rewrite Hz; rewrite Zabs_Zmult;
 replace (Zabs 2 * Zabs z)%Z with (Zabs z + Zabs z)%Z; 
 auto with zarith arith.
pattern (Zabs z) at 1 in |- *; replace (Zabs z) with (0 + Zabs z)%Z;
 auto with zarith.
rewrite (Zabs_eq 2); auto with zarith.
unfold FtoRradix, FtoR in |- *; simpl in |- *.
rewrite Hz; rewrite Rmult_IZR; simpl in |- *; ring.
Qed.
 
Theorem FNEvenD :
 forall p : float,
 Fbounded b p ->
 FNeven p -> exists q : float, Fbounded b q /\ p = (2%nat * q)%R :>R.
intros p H' H'0; case (FEvenD (Fnormalize radix b precision p));
 auto with float zarith arith.
intros x H'1; elim H'1; intros H'2 H'3; clear H'1; exists x; split; auto.
apply sym_eq.
rewrite <- H'3; auto.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
Qed.
End FOdd.
Hint Resolve FevenO FoddSuc FevenSuc FevenFop FoddFop FevenPred FoddPred
  FNevenFop FNoddFop FNoddSuc FNevenSuc FNevenPred FNoddPred: float.
