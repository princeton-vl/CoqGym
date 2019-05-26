(****************************************************************************
                                                                             
          IEEE754  :  Fmin                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Zenum.
Require Export FPred.
 
Section FMinMax.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Coercion FtoRradix : float >-> R.
Hypothesis radixMoreThanOne : (1 < radix)%Z.
 
Let radixMoreThanZERO := Zlt_1_O _ (Zlt_le_weak _ _ radixMoreThanOne).
Hint Resolve radixMoreThanZERO: zarith.
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
(* a function that returns a boundd greater than a given nat *)
 
Definition boundNat (n : nat) := Float 1%nat (digit radix n).
 
Theorem boundNatCorrect : forall n : nat, (n < boundNat n)%R.
intros n; unfold FtoRradix, FtoR, boundNat in |- *; simpl in |- *.
rewrite Rmult_1_l.
rewrite <- Zpower_nat_Z_powerRZ; auto with real zarith.
rewrite INR_IZR_INZ; auto with real zarith.
apply Rle_lt_trans with (Zabs n); [rewrite (Zabs_eq (Z_of_nat n))|idtac];auto with real zarith.
Qed.
 
Theorem boundBoundNat : forall n : nat, Fbounded b (boundNat n).
intros n; repeat split; unfold boundNat in |- *; simpl in |- *;
 auto with zarith.
apply vNumbMoreThanOne with (radix := radix) (precision := precision);
 auto with zarith.
apply Zle_trans with 0%Z;[case (dExp b)|idtac]; auto with zarith.
Qed.
(* A function that returns a bounded greater than a given r *)
 
Definition boundR (r : R) := boundNat (Zabs_nat (up (Rabs r))).
 
Theorem boundRCorrect1 : forall r : R, (r < boundR r)%R.
intros r; case (Rle_or_lt r 0); intros H'.
apply Rle_lt_trans with (1 := H').
unfold boundR, boundNat, FtoRradix, FtoR in |- *; simpl in |- *;
 auto with real.
rewrite Rmult_1_l; auto with real zarith.
apply Rlt_trans with (2 := boundNatCorrect (Zabs_nat (up (Rabs r)))).
replace (Rabs r) with r; auto with real.
apply Rlt_le_trans with (r2 := IZR (up r)); auto with real zarith.
case (archimed r); auto.
rewrite INR_IZR_INZ; auto with real zarith.
unfold Rabs in |- *; case (Rcase_abs r); auto with real.
intros H'0; Contradict H'0; auto with real.
Qed.
 
Theorem boundRrOpp : forall r : R, boundR r = boundR (- r).
intros R; unfold boundR in |- *.
rewrite Rabs_Ropp; auto.
Qed.
 
Theorem boundRCorrect2 : forall r : R, (Fopp (boundR r) < r)%R.
intros r; case (Rle_or_lt r 0); intros H'.
rewrite boundRrOpp.
pattern r at 2 in |- *; rewrite <- (Ropp_involutive r).
unfold FtoRradix in |- *; rewrite Fopp_correct.
apply Ropp_lt_contravar; apply boundRCorrect1; auto.
apply Rle_lt_trans with 0%R; auto.
replace 0%R with (-0)%R; auto with real.
unfold FtoRradix in |- *; rewrite Fopp_correct.
apply Ropp_le_contravar.
unfold boundR, boundNat, FtoRradix, FtoR in |- *; simpl in |- *;
 auto with real zarith.
rewrite Rmult_1_l; apply Rlt_le; auto with real zarith arith.
Qed.
(* A function that returns a list containing all the bounded smaller than a given real *)
 
Definition mBFloat (p : R) :=
  map (fun p : Z * Z => Float (fst p) (snd p))
    (mProd Z Z (Z * Z)
       (mZlist (- pPred (vNum b)) (pPred (vNum b)))
       (mZlist (- dExp b) (Fexp (boundR p)))).
 
Theorem mBFadic_correct1 :
 forall (r : R) (q : float),
 ~ is_Fzero q ->
 (Fopp (boundR r) < q)%R ->
 (q < boundR r)%R -> Fbounded b q -> In q (mBFloat r).
intros r q.
case (Zle_or_lt (Fexp (boundR r)) (Fexp q)); intros H'.
intros H'0 H'1 H'2 H'3; case H'0.
apply is_Fzero_rep2 with (radix := radix); auto.
rewrite <-
 FshiftCorrect with (n := Zabs_nat (Fexp q - Fexp (boundR r))) (x := q);
 auto with arith.
apply is_Fzero_rep1 with (radix := radix).
unfold is_Fzero in |- *.
cut (forall p : Z, (- 1%nat < p)%Z -> (p < 1%nat)%Z -> p = 0%Z);
 [ intros tmp; apply tmp | idtac ].
replace (- 1%nat)%Z with (Fnum (Fopp (boundR r))).
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with real zarith.
rewrite FshiftCorrect; auto.
unfold Fshift in |- *; simpl in |- *.
rewrite (fun x y => inj_abs (x - y)); auto with zarith.
simpl in |- *; auto.
replace (Z_of_nat 1) with (Fnum (boundR r)).
apply Rlt_Fexp_eq_Zlt with (radix := radix); auto with zarith.
rewrite FshiftCorrect; auto.
unfold Fshift in |- *; simpl in |- *.
rewrite inj_abs; auto with zarith.
generalize H'; simpl in |- *; auto with zarith.
simpl in |- *; auto.
intros p0; case p0; simpl in |- *; auto with zarith.
intros H'0 H'1 H'2 H'3; unfold mBFloat in |- *.
replace q with
 ((fun p : Z * Z => Float (fst p) (snd p)) (Fnum q, Fexp q)).
apply in_map with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
apply mProd_correct; auto.
apply mZlist_correct; auto with float.
apply Zle_Zabs_inv1; auto with float.
unfold pPred in |- *; apply Zle_Zpred; auto with float.
apply Zle_Zabs_inv2; auto with float.
unfold pPred in |- *; apply Zle_Zpred; auto with float.
apply mZlist_correct; auto with float.
auto with zarith.
case q; simpl in |- *; auto with zarith.
Qed.
 
Theorem mBFadic_correct2 : forall r : R, In (boundR r) (mBFloat r).
intros r; unfold mBFloat in |- *.
replace (boundR r) with
 ((fun p : Z * Z => Float (fst p) (snd p))
    (Fnum (boundR r), Fexp (boundR r))).
apply in_map with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
apply mProd_correct; auto.
apply mZlist_correct; auto.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
apply Zle_trans with (- (0))%Z; auto with zarith.
apply Zle_Zopp; unfold pPred in |- *; apply Zle_Zpred; simpl in |- *.
apply Zlt_trans with 1%Z; auto with zarith.
apply vNumbMoreThanOne with (3 := pGivesBound); auto.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
unfold pPred in |- *; apply Zle_Zpred; simpl in |- *.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
apply vNumbMoreThanOne with (3 := pGivesBound); auto.
apply mZlist_correct; auto.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
apply Zle_trans with 0%Z; auto with zarith arith.
case (dExp b); auto with zarith.
case (boundR r); simpl in |- *; auto with zarith.
case (boundR r); simpl in |- *; auto with zarith.
Qed.
 
Theorem mBFadic_correct3 : forall r : R, In (Fopp (boundR r)) (mBFloat r).
intros r; unfold mBFloat in |- *.
replace (Fopp (boundR r)) with
 ((fun p : Z * Z => Float (fst p) (snd p))
    (Fnum (Fopp (boundR r)), Fexp (Fopp (boundR r)))).
apply in_map with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
apply mProd_correct; auto.
apply mZlist_correct; auto.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
replace (-1)%Z with (- Z_of_nat 1)%Z; auto with zarith.
apply Zle_Zopp.
unfold pPred in |- *; apply Zle_Zpred; simpl in |- *.
apply (vNumbMoreThanOne radix) with (precision := precision);
 auto with zarith.
unfold pPred in |- *; apply Zle_Zpred; simpl in |- *.
red in |- *; simpl in |- *; auto.
apply mZlist_correct; auto.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
apply Zle_trans with 0%Z; auto with zarith.
case (dExp b); auto with zarith.
case (boundR r); simpl in |- *; auto with zarith.
case (boundR r); simpl in |- *; auto with zarith.
Qed.
 
Theorem mBFadic_correct4 :
 forall r : R, In (Float 0%nat (- dExp b)) (mBFloat r).
intros p; unfold mBFloat in |- *.
replace (Float 0%nat (- dExp b)) with
 ((fun p : Z * Z => Float (fst p) (snd p))
    (Fnum (Float 0%nat (- dExp b)), Fexp (Float 0%nat (- dExp b)))).
apply in_map with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
apply mProd_correct; auto.
apply mZlist_correct; auto.
simpl in |- *; auto with zarith.
replace 0%Z with (- (0))%Z; [ idtac | simpl in |- *; auto ].
apply Zle_Zopp; unfold pPred in |- *; apply Zle_Zpred.
red in |- *; simpl in |- *; auto with zarith.
simpl in |- *; auto with zarith.
unfold pPred in |- *; apply Zle_Zpred.
red in |- *; simpl in |- *; auto with zarith.
apply mZlist_correct; auto.
simpl in |- *; auto with zarith.
unfold boundR, boundNat in |- *; simpl in |- *; auto with zarith.
apply Zle_trans with 0%Z; auto with zarith.
case (dExp b); auto with zarith.
simpl in |- *; auto with zarith.
Qed.
 
Theorem mBPadic_Fbounded :
 forall (p : float) (r : R), In p (mBFloat r) -> Fbounded b p.
intros p r H'; red in |- *; repeat (split; auto).
apply Zpred_Zle_Zabs_intro.
apply mZlist_correct_rev1 with (q := Zpred (Zpos (vNum b)));
 auto with real.
apply
 mProd_correct_rev1
  with
    (l2 := mZlist (- dExp b) (Fexp (boundR r)))
    (C := (Z * Z)%type)
    (b := Fexp p); auto.
apply
 in_map_inv with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
intros a1 b1; case a1; case b1; simpl in |- *.
intros z z0 z1 z2 H'0; inversion H'0; auto.
generalize H'; case p; auto.
apply mZlist_correct_rev2 with (p := (- Zpred (Zpos (vNum b)))%Z);
 auto.
apply
 mProd_correct_rev1
  with
    (l2 := mZlist (- dExp b) (Fexp (boundR r)))
    (C := (Z * Z)%type)
    (b := Fexp p); auto.
apply
 in_map_inv with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
intros a1 b1; case a1; case b1; simpl in |- *.
intros z z0 z1 z2 H'0; inversion H'0; auto.
generalize H'; case p; auto.
apply mZlist_correct_rev1 with (q := Fexp (boundR r)); auto.
apply
 mProd_correct_rev2
  with
    (l1 := mZlist (- pPred (vNum b)) (pPred (vNum b)))
    (C := (Z * Z)%type)
    (a := Fnum p); auto.
apply
 in_map_inv with (f := fun p : Z * Z => Float (fst p) (snd p));
 auto.
intros a1 b1; case a1; case b1; simpl in |- *.
intros z z0 z1 z2 H'0; inversion H'0; auto.
generalize H'; case p; auto.
Qed.
(* Some general properties of rounded predicate :
   -Projector A bounded is rounded to something equal to itself 
  - Monotone : the rounded predicate is monotone *)
 
Definition ProjectorP (P : R -> float -> Prop) :=
  forall p q : float, Fbounded b p -> P p q -> p = q :>R.
 
Definition MonotoneP (P : R -> float -> Prop) :=
  forall (p q : R) (p' q' : float),
  (p < q)%R -> P p p' -> P q q' -> (p' <= q')%R.
(* What it is to be a minimum*)
 
Definition isMin (r : R) (min : float) :=
  Fbounded b min /\
  (min <= r)%R /\
  (forall f : float, Fbounded b f -> (f <= r)%R -> (f <= min)%R).
(* Min is a projector *)
 
Theorem isMin_inv1 : forall (p : float) (r : R), isMin r p -> (p <= r)%R.
intros p r H; case H; intros H1 H2; case H2; auto.
Qed.
 
Theorem ProjectMin : ProjectorP isMin.
red in |- *.
intros p q H' H'0; apply Rle_antisym.
elim H'0; intros H'1 H'2; elim H'2; intros H'3 H'4; apply H'4; clear H'2;
 auto with real.
apply isMin_inv1 with (1 := H'0); auto.
Qed.
(* It is monotone *)
 
Theorem MonotoneMin : MonotoneP isMin.
red in |- *.
intros p q p' q' H' H'0 H'1.
elim H'1; intros H'2 H'3; elim H'3; intros H'4 H'5; apply H'5; clear H'3 H'1;
 auto.
case H'0; auto.
apply Rle_trans with p; auto.
apply isMin_inv1 with (1 := H'0); auto.
apply Rlt_le; auto.
Qed.
(* What it is to be a maximum *)
 
Definition isMax (r : R) (max : float) :=
  Fbounded b max /\
  (r <= max)%R /\
  (forall f : float, Fbounded b f -> (r <= f)%R -> (max <= f)%R).
(* It is a projector *)
 
Theorem isMax_inv1 : forall (p : float) (r : R), isMax r p -> (r <= p)%R.
intros p r H; case H; intros H1 H2; case H2; auto.
Qed.
 
Theorem ProjectMax : ProjectorP isMax.
red in |- *.
intros p q H' H'0; apply Rle_antisym.
apply isMax_inv1 with (1 := H'0); auto.
elim H'0; intros H'1 H'2; elim H'2; intros H'3 H'4; apply H'4; clear H'2;
 auto with real.
Qed.
(* It is monotone *)
 
Theorem MonotoneMax : MonotoneP isMax.
red in |- *.
intros p q p' q' H' H'0 H'1.
elim H'0; intros H'2 H'3; elim H'3; intros H'4 H'5; apply H'5; clear H'3 H'0.
case H'1; auto.
apply Rle_trans with q; auto.
apply Rlt_le; auto.
apply isMax_inv1 with (1 := H'1); auto.
Qed.
(* Minimun is defined upto equality *)
 
Theorem MinEq :
 forall (p q : float) (r : R), isMin r p -> isMin r q -> p = q :>R.
intros p q r H' H'0; apply Rle_antisym.
elim H'0; intros H'1 H'2; elim H'2; intros H'3 H'4; apply H'4; clear H'2 H'0;
 auto.
case H'; auto.
apply isMin_inv1 with (1 := H'); auto.
elim H'; intros H'1 H'2; elim H'2; intros H'3 H'4; apply H'4; clear H'2 H';
 auto.
case H'0; auto.
apply isMin_inv1 with (1 := H'0); auto.
Qed.
(* Maximum is defined upto equality *)
 
Theorem MaxEq :
 forall (p q : float) (r : R), isMax r p -> isMax r q -> p = q :>R.
intros p q r H' H'0; apply Rle_antisym.
elim H'; intros H'1 H'2; elim H'2; intros H'3 H'4; apply H'4; clear H'2 H';
 auto.
case H'0; auto.
apply isMax_inv1 with (1 := H'0); auto.
elim H'0; intros H'1 H'2; elim H'2; intros H'3 H'4; apply H'4; clear H'2 H'0;
 auto.
case H'; auto.
apply isMax_inv1 with (1 := H'); auto.
Qed.
(* Min and Max are related *)
 
Theorem MinOppMax :
 forall (p : float) (r : R), isMin r p -> isMax (- r) (Fopp p).
intros p r H'; split.
apply oppBounded; case H'; auto.
split.
unfold FtoRradix in |- *; rewrite Fopp_correct.
apply Ropp_le_contravar; apply isMin_inv1 with (1 := H'); auto.
intros f H'0 H'1.
rewrite <- (Fopp_Fopp f).
unfold FtoRradix in |- *; rewrite Fopp_correct; rewrite Fopp_correct.
apply Ropp_le_contravar.
elim H'.
intros H'2 H'3; elim H'3; intros H'4 H'5; apply H'5; clear H'3.
apply oppBounded; case H'; auto.
rewrite <- (Ropp_involutive r).
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
Qed.
(* Max and Min are related *)
 
Theorem MaxOppMin :
 forall (p : float) (r : R), isMax r p -> isMin (- r) (Fopp p).
intros p r H'; split.
apply oppBounded; case H'; auto.
split.
unfold FtoRradix in |- *; rewrite Fopp_correct.
apply Ropp_le_contravar; apply isMax_inv1 with (1 := H'); auto.
intros f H'0 H'1.
rewrite <- (Fopp_Fopp f).
unfold FtoRradix in |- *; repeat rewrite Fopp_correct.
apply Ropp_le_contravar.
rewrite <- (Fopp_correct radix f).
elim H'.
intros H'2 H'3; elim H'3; intros H'4 H'5; apply H'5; clear H'3.
apply oppBounded; auto.
rewrite <- (Ropp_involutive r).
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
Qed.
(* If I have a strict min I can get a max using FNSucc *)
 
Theorem MinMax :
 forall (p : float) (r : R),
 isMin r p -> r <> p :>R -> isMax r (FNSucc b radix precision p).
intros p r H' H'0.
split.
apply FcanonicBound with (radix := radix); auto with float.
apply FNSuccCanonic; auto.
inversion H'; auto.
split.
case (Rle_or_lt (FNSucc b radix precision p) r); intros H'2; auto.
absurd (FNSucc b radix precision p <= p)%R.
apply Rlt_not_le.
unfold FtoRradix in |- *; apply FNSuccLt; auto.
inversion H'; auto.
elim H0; intros H'1 H'3; apply H'3; auto.
apply FcanonicBound with (radix := radix); auto with float.
apply Rlt_le; auto.
intros f H'2 H'3.
replace (FtoRradix f) with (FtoRradix (Fnormalize radix b precision f)).
unfold FtoRradix in |- *; apply FNSuccProp; auto.
inversion H'; auto.
apply FcanonicBound with (radix := radix); auto with float.
apply Rlt_le_trans with r; auto.
case (Rle_or_lt r p); auto.
intros H'4; Contradict H'0.
apply Rle_antisym; auto; apply isMin_inv1 with (1 := H'); auto.
rewrite FnormalizeCorrect; auto.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
Qed.
(* Find a minimun in a given list if it exists *)
 
Theorem MinExList :
 forall (r : R) (L : list float),
 (forall f : float, In f L -> (r < f)%R) \/
 (exists min : float,
    In min L /\
    (min <= r)%R /\ (forall f : float, In f L -> (f <= r)%R -> (f <= min)%R)).
intros r L; elim L; simpl in |- *; auto.
left; intros f H'; elim H'.
intros a l H'.
elim H';
 [ intros H'0; clear H'
 | intros H'0; elim H'0; intros min E; elim E; intros H'1 H'2; elim H'2;
    intros H'3 H'4; try exact H'4; clear H'2 E H'0 H' ].
case (Rle_or_lt a r); intros H'1.
right; exists a; repeat split; auto.
intros f H'; elim H';
 [ intros H'2; rewrite <- H'2; clear H' | intros H'2; clear H' ];
 auto with real.
intros H'; Contradict H'; auto with real.
apply Rlt_not_le; auto with real.
left; intros f H'; elim H';
 [ intros H'2; rewrite <- H'2; clear H' | intros H'2; clear H' ]; 
 auto.
case (Rle_or_lt a min); intros H'5.
right; exists min; repeat split; auto.
intros f H'; elim H';
 [ intros H'0; rewrite <- H'0; clear H' | intros H'0; clear H' ]; 
 auto.
case (Rle_or_lt a r); intros H'6.
right; exists a; repeat split; auto.
intros f H'; elim H';
 [ intros H'0; rewrite <- H'0; clear H' | intros H'0; clear H' ];
 auto with real.
intros H'; apply Rle_trans with (FtoRradix min); auto with real.
right; exists min; split; auto; split; auto.
intros f H'; elim H';
 [ intros H'0; elim H'0; clear H' | intros H'0; clear H' ]; 
 auto.
intros H'; Contradict H'6; auto with real.
apply Rle_not_lt; auto.
Qed.
 
Theorem MinEx : forall r : R, exists min : float, isMin r min.
intros r.
case (MinExList r (mBFloat r)).
intros H'0; absurd (Fopp (boundR r) <= r)%R; auto.
apply Rlt_not_le.
apply H'0.
apply mBFadic_correct3; auto.
(* A minimum always exists *)
apply Rlt_le.
apply boundRCorrect2; auto.
intros H'0; elim H'0; intros min E; elim E; intros H'1 H'2; elim H'2;
 intros H'3 H'4; clear H'2 E H'0.
exists min; split; auto.
apply mBPadic_Fbounded with (r := r); auto.
split; auto.
intros f H'0 H'2.
case (Req_dec f 0); intros H'6.
replace (FtoRradix f) with (FtoRradix (Float 0%nat (- dExp b))).
apply H'4; auto.
apply mBFadic_correct4; auto.
replace (FtoRradix (Float 0%nat (- dExp b))) with (FtoRradix f); auto.
rewrite H'6.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto with real.
rewrite H'6.
unfold FtoRradix, FtoR in |- *; simpl in |- *; auto with real.
case (Rle_or_lt f (Fopp (boundR r))); intros H'5.
apply Rle_trans with (FtoRradix (Fopp (boundR r))); auto.
apply H'4; auto.
apply mBFadic_correct3; auto.
apply Rlt_le.
apply boundRCorrect2; auto.
case (Rle_or_lt (boundR r) f); intros H'7.
Contradict H'2; apply Rlt_not_le.
apply Rlt_le_trans with (FtoRradix (boundR r)); auto.
apply boundRCorrect1; auto.
apply H'4; auto.
apply mBFadic_correct1; auto.
Contradict H'6; unfold FtoRradix in |- *; apply is_Fzero_rep1; auto.
Qed.
 
Theorem MaxEx : forall r : R, exists max : float, isMax r max.
intros r; case (MinEx r).
intros x H'.
case (Req_dec x r); intros H'1.
exists x.
rewrite <- H'1.
red in |- *; split; [ case H' | split ]; auto with real.
(* A maximum always exists *)
exists (FNSucc b radix precision x).
apply MinMax; auto.
Qed.
 
Theorem MinBinade :
 forall (r : R) (p : float),
 Fbounded b p ->
 (p <= r)%R -> (r < FNSucc b radix precision p)%R -> isMin r p.
intros r p H' H'0 H'1.
split; auto.
split; auto.
intros f H'2 H'3.
case (Rle_or_lt f p); auto; intros H'5.
Contradict H'3.
(* If we are between a bound and its successor, it is our minimum *)
apply Rlt_not_le.
apply Rlt_le_trans with (1 := H'1); auto with real.
replace (FtoRradix f) with (FtoRradix (Fnormalize radix b precision f)).
unfold FtoRradix in |- *; apply FNSuccProp; auto; try apply FnormalizeCanonic;
 auto.
unfold FtoRradix in |- *; repeat rewrite FnormalizeCorrect; auto with real.
apply FcanonicBound with (radix := radix); auto.
apply FnormalizeCanonic; auto.
unfold FtoRradix in |- *; rewrite FnormalizeCorrect; auto with real.
unfold FtoRradix in |- *; rewrite FnormalizeCorrect; auto with real.
Qed.
 
Theorem FminRep :
 forall p q : float,
 isMin p q -> exists m : Z, q = Float m (Fexp p) :>R.
intros p q H'.
replace (FtoRradix q) with (FtoRradix (Fnormalize radix b precision q)).
2: unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
case (Zle_or_lt (Fexp (Fnormalize radix b precision q)) (Fexp p)); intros H'1.
exists (Fnum p).
unfold FtoRradix in |- *; apply FSuccZleEq with (3 := pGivesBound); auto.
(* A min of a float is always represnetable with the same exposant *)
replace (Float (Fnum p) (Fexp p)) with p; [ idtac | case p ]; auto.
replace (FtoR radix (Fnormalize radix b precision q)) with (FtoR radix q);
 [ idtac | rewrite FnormalizeCorrect ]; auto.
apply isMin_inv1 with (1 := H'); auto.
replace (FSucc b radix precision (Fnormalize radix b precision q)) with
 (FNSucc b radix precision q); [ idtac | case p ]; 
 auto.
replace (Float (Fnum p) (Fexp p)) with p; [ idtac | case p ]; auto.
case (Req_dec p q); intros Eq0.
unfold FtoRradix in Eq0; rewrite Eq0.
apply FNSuccLt; auto.
case (MinMax q p); auto.
intros H'2 H'3; elim H'3; intros H'4 H'5; clear H'3.
case H'4; auto.
intros H'0; absurd (p <= q)%R; rewrite H'0; auto.
apply Rlt_not_le; auto.
unfold FtoRradix in |- *; apply FNSuccLt; auto.
inversion H'.
elim H0; intros H'3 H'6; apply H'6; clear H0; auto.
rewrite <- H'0; auto with real.
exists
 (Fnum
    (Fshift radix (Zabs_nat (Fexp (Fnormalize radix b precision q) - Fexp p))
       (Fnormalize radix b precision q))).
pattern (Fexp p) at 2 in |- *;
 replace (Fexp p) with
  (Fexp
     (Fshift radix
        (Zabs_nat (Fexp (Fnormalize radix b precision q) - Fexp p))
        (Fnormalize radix b precision q))).
unfold FtoRradix in |- *;
 rewrite <-
  FshiftCorrect
                with
                (n := 
                  Zabs_nat (Fexp (Fnormalize radix b precision q) - Fexp p))
               (x := Fnormalize radix b precision q).
case
 (Fshift radix (Zabs_nat (Fexp (Fnormalize radix b precision q) - Fexp p))
    (Fnormalize radix b precision q)); auto.
auto with arith.
simpl in |- *; rewrite inj_abs; auto with zarith.
Qed.
 
Theorem MaxBinade :
 forall (r : R) (p : float),
 Fbounded b p ->
 (r <= p)%R -> (FNPred b radix precision p < r)%R -> isMax r p.
intros r p H' H'0 H'1.
rewrite <- (Ropp_involutive r).
rewrite <- (Fopp_Fopp p).
apply MinOppMax.
apply MinBinade; auto with real float.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real.
(* Same for max *)
rewrite <- (Fopp_Fopp (FNSucc b radix precision (Fopp p))).
rewrite <- FNPredFopFNSucc; auto.
unfold FtoRradix in |- *; rewrite Fopp_correct; auto with real arith.
Qed.
 
Theorem MaxMin :
 forall (p : float) (r : R),
 isMax r p -> r <> p :>R -> isMin r (FNPred b radix precision p).
intros p r H' H'0.
rewrite <- (Fopp_Fopp (FNPred b radix precision p)).
rewrite <- (Ropp_involutive r).
apply MaxOppMin.
rewrite FNPredFopFNSucc; auto.
rewrite Fopp_Fopp; auto.
(* Taking the pred of a max we get a min *)
apply MinMax; auto.
apply MaxOppMin; auto.
Contradict H'0.
rewrite <- (Ropp_involutive r); rewrite H'0; auto; unfold FtoRradix in |- *;
 rewrite Fopp_correct; auto; apply Ropp_involutive.
Qed.
 
Theorem FmaxRep :
 forall p q : float,
 isMax p q -> exists m : Z, q = Float m (Fexp p) :>R.
intros p q H'; case (FminRep (Fopp p) (Fopp q)).
unfold FtoRradix in |- *; rewrite Fopp_correct.
apply MaxOppMin; auto.
intros x H'0.
exists (- x)%Z.
rewrite <- (Ropp_involutive (FtoRradix q)).
(* The max of a float can be represented with the same exposant *)
unfold FtoRradix in |- *; rewrite <- Fopp_correct.
unfold FtoRradix in H'0; rewrite H'0.
unfold FtoR in |- *; simpl in |- *; auto with real.
rewrite Ropp_Ropp_IZR; rewrite Ropp_mult_distr_l_reverse; auto.
Qed.
 
End FMinMax.
Hint Resolve ProjectMax MonotoneMax MinOppMax MaxOppMin MinMax MinBinade
  MaxBinade MaxMin: float.
