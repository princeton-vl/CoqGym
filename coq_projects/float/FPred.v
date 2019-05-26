(****************************************************************************
                                                                             
          IEEE754  :  FPred                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export FSucc.
Section pred.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionNotZero : precision <> 0.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Definition FPred (x : float) :=
  match Z_eq_bool (Fnum x) (- pPred (vNum b)) with
  | true => Float (- nNormMin radix precision) (Zsucc (Fexp x))
  | false =>
      match Z_eq_bool (Fnum x) (nNormMin radix precision) with
      | true =>
          match Z_eq_bool (Fexp x) (- dExp b) with
          | true => Float (Zpred (Fnum x)) (Fexp x)
          | false => Float (pPred (vNum b)) (Zpred (Fexp x))
          end
      | false => Float (Zpred (Fnum x)) (Fexp x)
      end
  end.
 
Theorem FPredSimpl1 :
 forall x : float,
 Fnum x = (- pPred (vNum b))%Z ->
 FPred x = Float (- nNormMin radix precision) (Zsucc (Fexp x)).
intros x H'; unfold FPred in |- *.
generalize (Z_eq_bool_correct (Fnum x) (- pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (- pPred (vNum b))); auto.
intros H'0; Contradict H'0; auto.
Qed.
 
Theorem FPredSimpl2 :
 forall x : float,
 Fnum x = nNormMin radix precision ->
 Fexp x <> (- dExp b)%Z -> FPred x = Float (pPred (vNum b)) (Zpred (Fexp x)).
intros x H' H'0; unfold FPred in |- *.
generalize (Z_eq_bool_correct (Fnum x) (- pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (- pPred (vNum b))); auto.
intros H'1; absurd (0%nat < Fnum x)%Z; auto with zarith arith.
apply Zle_not_lt; rewrite H'1; replace (Z_of_nat 0) with (- (0))%Z;
 [ apply Zle_Zopp | simpl in |- *; auto ].
unfold pPred in |- *; apply Zle_Zpred; red in |- *; simpl in |- *; auto.
rewrite H'.
apply nNormPos; auto with zarith.
intros H'1;
 generalize (Z_eq_bool_correct (Fnum x) (nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (nNormMin radix precision)).
intros H'2; generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); auto.
intros H'3; Contradict H'0; auto.
intros H'2; Contradict H'2; auto.
Qed.
 
Theorem FPredSimpl3 :
 FPred (Float (nNormMin radix precision) (- dExp b)) =
 Float (Zpred (nNormMin radix precision)) (- dExp b).
unfold FPred in |- *; simpl in |- *.
generalize (Z_eq_bool_correct (nNormMin radix precision) (- pPred (vNum b)));
 case (Z_eq_bool (nNormMin radix precision) (- pPred (vNum b))); 
 auto.
intros H'0; absurd (0 < pPred (vNum b))%Z; auto with zarith arith.
rewrite <- (Zopp_involutive (pPred (vNum b))); rewrite <- H'0.
apply Zle_not_lt; replace 0%Z with (- (0))%Z;
 [ apply Zle_Zopp | simpl in |- *; auto ].
apply Zlt_le_weak; apply nNormPos; auto with float zarith.
unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *;
 auto with float zarith.
simpl in |- *; apply vNumbMoreThanOne with (3 := pGivesBound); auto.
intros H';
 generalize
  (Z_eq_bool_correct (nNormMin radix precision) (nNormMin radix precision));
 case (Z_eq_bool (nNormMin radix precision) (nNormMin radix precision)).
intros H'0; generalize (Z_eq_bool_correct (- dExp b) (- dExp b));
 case (Z_eq_bool (- dExp b) (- dExp b)); auto.
intros H'1; Contradict H'1; auto.
intros H'1; Contradict H'1; auto.
Qed.
 
Theorem FPredSimpl4 :
 forall x : float,
 Fnum x <> (- pPred (vNum b))%Z ->
 Fnum x <> nNormMin radix precision ->
 FPred x = Float (Zpred (Fnum x)) (Fexp x).
intros x H' H'0; unfold FPred in |- *.
generalize (Z_eq_bool_correct (Fnum x) (- pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (- pPred (vNum b))); auto.
intros H'1; Contradict H'; auto.
intros H'1;
 generalize (Z_eq_bool_correct (Fnum x) (nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (nNormMin radix precision)); 
 auto.
intros H'2; Contradict H'0; auto.
Qed.
 
Theorem FPredFopFSucc :
 forall x : float, FPred x = Fopp (FSucc b radix precision (Fopp x)).
intros x.
generalize (Z_eq_bool_correct (Fnum x) (- pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (- pPred (vNum b))); intros H'1.
rewrite FPredSimpl1; auto; rewrite FSuccSimpl1; auto.
unfold Fopp in |- *; simpl in |- *; rewrite H'1; auto with zarith.
generalize (Z_eq_bool_correct (Fnum x) (nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (nNormMin radix precision)); 
 intros H'2.
generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); intros H'3.
replace x with (Float (Fnum x) (Fexp x)).
rewrite H'2; rewrite H'3; rewrite FPredSimpl3; unfold Fopp in |- *;
 simpl in |- *; rewrite FSuccSimpl3; simpl in |- *; 
 auto.
rewrite <- Zopp_Zpred_Zs; rewrite Zopp_involutive; auto.
case x; simpl in |- *; auto.
rewrite FPredSimpl2; auto; rewrite FSuccSimpl2; unfold Fopp in |- *;
 simpl in |- *; try rewrite Zopp_involutive; 
 auto.
rewrite H'2; auto.
rewrite FPredSimpl4; auto; rewrite FSuccSimpl4; auto.
unfold Fopp in |- *; simpl in |- *; rewrite <- Zopp_Zpred_Zs;
 rewrite Zopp_involutive; auto.
unfold Fopp in |- *; simpl in |- *; Contradict H'1; rewrite <- H'1;
 rewrite Zopp_involutive; auto.
unfold Fopp in |- *; simpl in |- *; Contradict H'2; auto with zarith.
Qed.
 
Theorem FPredDiff1 :
 forall x : float,
 Fnum x <> nNormMin radix precision ->
 Fminus radix x (FPred x) = Float 1%nat (Fexp x) :>R.
intros x H'; rewrite (FPredFopFSucc x).
pattern x at 1 in |- *; rewrite <- (Fopp_Fopp x).
rewrite <- Fopp_Fminus_dist.
rewrite Fopp_Fminus.
unfold FtoRradix in |- *; rewrite FSuccDiff1; auto.
replace (Fnum (Fopp x)) with (- Fnum x)%Z.
Contradict H'; rewrite <- (Zopp_involutive (Fnum x)); rewrite H';
 auto with zarith.
case x; simpl in |- *; auto.
Qed.
 
Theorem FPredDiff2 :
 forall x : float,
 Fnum x = nNormMin radix precision ->
 Fexp x = (- dExp b)%Z -> Fminus radix x (FPred x) = Float 1%nat (Fexp x) :>R.
intros x H' H'0; rewrite (FPredFopFSucc x).
pattern x at 1 in |- *; rewrite <- (Fopp_Fopp x).
rewrite <- Fopp_Fminus_dist.
rewrite Fopp_Fminus.
unfold FtoRradix in |- *; rewrite FSuccDiff2; auto.
rewrite <- H'; case x; auto.
Qed.
 
Theorem FPredDiff3 :
 forall x : float,
 Fnum x = nNormMin radix precision ->
 Fexp x <> (- dExp b)%Z ->
 Fminus radix x (FPred x) = Float 1%nat (Zpred (Fexp x)) :>R.
intros x H' H'0; rewrite (FPredFopFSucc x).
pattern x at 1 in |- *; rewrite <- (Fopp_Fopp x).
rewrite <- Fopp_Fminus_dist.
rewrite Fopp_Fminus.
unfold FtoRradix in |- *; rewrite FSuccDiff3; auto.
rewrite <- H'; case x; auto.
Qed.
 
Theorem FBoundedPred : forall f : float, Fbounded b f -> Fbounded b (FPred f).
intros f H'; rewrite (FPredFopFSucc f); auto with float.
Qed.
 
Theorem FPredCanonic :
 forall a : float, Fcanonic radix b a -> Fcanonic radix b (FPred a).
intros a H'.
rewrite FPredFopFSucc; auto with float.
Qed.
 
Theorem FPredLt : forall a : float, (FPred a < a)%R.
intros a; rewrite FPredFopFSucc.
pattern a at 2 in |- *; rewrite <- (Fopp_Fopp a).
unfold FtoRradix in |- *; repeat rewrite Fopp_correct.
apply Ropp_lt_contravar.
rewrite <- Fopp_correct; auto with float.
Qed.
 
Theorem R0RltRlePred : forall x : float, (0 < x)%R -> (0 <= FPred x)%R.
intros x H'; rewrite FPredFopFSucc.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct.
replace 0%R with (-0)%R; auto with real.
apply Ropp_le_contravar.
apply R0RltRleSucc; auto.
unfold FtoRradix in |- *; repeat rewrite Fopp_correct.
replace 0%R with (-0)%R; auto with real.
Qed.
 
Theorem FPredProp :
 forall x y : float,
 Fcanonic radix b x -> Fcanonic radix b y -> (x < y)%R -> (x <= FPred y)%R.
intros x y H' H'0 H'1; rewrite FPredFopFSucc.
rewrite <- (Fopp_Fopp x).
unfold FtoRradix in |- *; rewrite Fopp_correct with (x := Fopp x).
rewrite Fopp_correct with (x := FSucc b radix precision (Fopp y));
 auto with float real.
apply Ropp_le_contravar.
apply FSuccProp; auto with float.
repeat rewrite Fopp_correct; auto with real.
Qed.
 
Theorem FPredZleEq :
 forall p q : float,
 (FPred p < q)%R -> (q <= p)%R -> (Fexp p <= Fexp q)%Z -> p = q :>R.
intros p q H' H'0 H'1.
rewrite <- (Ropp_involutive p); rewrite <- (Ropp_involutive q);
 apply Ropp_eq_compat.
unfold FtoRradix in |- *; repeat rewrite <- Fopp_correct.
apply FSuccZleEq with (b := b) (precision := precision); auto.
repeat rewrite Fopp_correct; auto with real.
apply Ropp_lt_cancel.
repeat rewrite <- Fopp_correct; rewrite <- FPredFopFSucc; rewrite Fopp_Fopp;
 auto.
Qed.
 
Definition FNPred (x : float) := FPred (Fnormalize radix b precision x).
 
Theorem FNPredFopFNSucc :
 forall x : float, FNPred x = Fopp (FNSucc b radix precision (Fopp x)).
intros x; unfold FNPred, FNSucc in |- *; auto.
rewrite Fnormalize_Fopp; auto.
apply FPredFopFSucc; auto.
Qed.
 
Theorem FNPredCanonic :
 forall a : float, Fbounded b a -> Fcanonic radix b (FNPred a).
intros a H'; unfold FNPred in |- *.
apply FPredCanonic; auto with float.
Qed.
 
Theorem FNPredLt : forall a : float, (FNPred a < a)%R.
intros a; unfold FNPred in |- *.
unfold FtoRradix in |- *;
 rewrite <- (FnormalizeCorrect _ radixMoreThanOne b precision a).
apply FPredLt; auto.
Qed.
 
Theorem FNPredProp :
 forall x y : float,
 Fbounded b x -> Fbounded b y -> (x < y)%R -> (x <= FNPred y)%R.
intros x y H' H'0 H'1; unfold FNPred in |- *.
replace (FtoRradix x) with (FtoRradix (Fnormalize radix b precision x)).
apply FPredProp; auto with float.
unfold FtoRradix in |- *; repeat rewrite FnormalizeCorrect; auto.
unfold FtoRradix in |- *; repeat rewrite FnormalizeCorrect; auto.
Qed.
 
Theorem FPredSuc :
 forall x : float,
 Fcanonic radix b x -> FPred (FSucc b radix precision x) = x.
intros x H; unfold FPred, FSucc in |- *.
cut (Fbounded b x); [ intros Fb0 | apply FcanonicBound with (1 := H) ].
generalize (Z_eq_bool_correct (Fnum x) (pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (pPred (vNum b))); simpl in |- *.
generalize (Z_eq_bool_correct (nNormMin radix precision) (- pPred (vNum b)));
 case (Z_eq_bool (nNormMin radix precision) (- pPred (vNum b)));
 simpl in |- *.
intros H'; Contradict H'; apply sym_not_equal; apply Zlt_not_eq; auto.
apply Zlt_le_trans with (- 0%nat)%Z.
apply Zlt_Zopp; unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *;
 apply vNumbMoreThanOne with (3 := pGivesBound); auto.
simpl in |- *; apply Zlt_le_weak; apply nNormPos; auto.
generalize
 (Z_eq_bool_correct (nNormMin radix precision) (nNormMin radix precision));
 case (Z_eq_bool (nNormMin radix precision) (nNormMin radix precision));
 simpl in |- *.
generalize (Z_eq_bool_correct (Zsucc (Fexp x)) (- dExp b));
 case (Z_eq_bool (Zsucc (Fexp x)) (- dExp b)); simpl in |- *.
intros H' H'0 H'1 H'2; absurd (- dExp b <= Fexp x)%Z; auto with float.
rewrite <- H'; auto with float zarith.
replace (Zpred (Zsucc (Fexp x))) with (Fexp x);
 [ idtac | unfold Zsucc, Zpred in |- *; ring ]; auto.
intros H' H'0 H'1 H'2; rewrite <- H'2; auto.
apply floatEq; auto.
intros H'; case H'; auto.
generalize (Z_eq_bool_correct (Fnum x) (- nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (- nNormMin radix precision)); 
 simpl in |- *.
generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); simpl in |- *.
generalize (Z_eq_bool_correct (Zsucc (Fnum x)) (- pPred (vNum b)));
 case (Z_eq_bool (Zsucc (Fnum x)) (- pPred (vNum b))); 
 simpl in |- *.
intros H0 H1 H2; absurd (Zsucc (Fnum x) <= Fnum x)%Z; auto with zarith.
rewrite H0; rewrite H2; (apply Zle_Zopp; auto with float arith).
unfold pPred in |- *; apply Zle_Zpred; apply ZltNormMinVnum; auto with zarith.
generalize (Z_eq_bool_correct (Zsucc (Fnum x)) (nNormMin radix precision));
 case (Z_eq_bool (Zsucc (Fnum x)) (nNormMin radix precision)); 
 simpl in |- *.
intros H' H'0 H'1 H'2; Contradict H'2.
rewrite <- H'; auto with zarith.
replace (Zpred (Zsucc (Fnum x))) with (Fnum x);
 [ idtac | unfold Zsucc, Zpred in |- *; ring ]; auto.
intros H' H'0 H'1 H'2 H'3; apply floatEq; auto.
generalize (Z_eq_bool_correct (- pPred (vNum b)) (- pPred (vNum b)));
 case (Z_eq_bool (- pPred (vNum b)) (- pPred (vNum b))); 
 auto.
intros H' H'0 H'1 H'2; rewrite <- H'1.
replace (Zsucc (Zpred (Fexp x))) with (Fexp x);
 [ idtac | unfold Zsucc, Zpred in |- *; ring ]; auto.
apply floatEq; auto.
intros H'; case H'; auto.
generalize (Z_eq_bool_correct (Zsucc (Fnum x)) (- pPred (vNum b)));
 case (Z_eq_bool (Zsucc (Fnum x)) (- pPred (vNum b))); 
 simpl in |- *.
intros H'; absurd (- pPred (vNum b) <= Fnum x)%Z; auto with float.
rewrite <- H'; auto with zarith.
apply Zle_Zabs_inv1; auto with float.
unfold pPred in |- *; apply Zle_Zpred; auto with float.
generalize (Z_eq_bool_correct (Zsucc (Fnum x)) (nNormMin radix precision));
 case (Z_eq_bool (Zsucc (Fnum x)) (nNormMin radix precision)); 
 simpl in |- *.
generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); simpl in |- *.
intros H' H'0 H'1 H'2 H'3.
replace (Zpred (Zsucc (Fnum x))) with (Fnum x);
 [ idtac | unfold Zsucc, Zpred in |- *; ring ]; auto.
apply floatEq; auto.
intros H' H'0 H'1 H'2 H'3; case H.
intros H'4; absurd (nNormMin radix precision <= Zabs (Fnum x))%Z.
replace (Fnum x) with (Zpred (Zsucc (Fnum x)));
 [ idtac | unfold Zsucc, Zpred in |- *; ring ]; auto.
rewrite H'0.
apply Zlt_not_le; rewrite Zabs_eq; auto with zarith.
apply Zle_Zpred; apply nNormPos; auto with float zarith.
apply pNormal_absolu_min with (b := b); auto.
intros H'4; Contradict H'; apply FsubnormalFexp with (1 := H'4).
intros H' H'0 H'1 H'2; apply floatEq; simpl in |- *; auto.
unfold Zpred, Zsucc in |- *; ring.
Qed.
 
Theorem FSucPred :
 forall x : float,
 Fcanonic radix b x -> FSucc b radix precision (FPred x) = x.
intros x H; unfold FPred, FSucc in |- *.
cut (Fbounded b x); [ intros Fb0 | apply FcanonicBound with (1 := H) ].
generalize (Z_eq_bool_correct (Fnum x) (- pPred (vNum b)));
 case (Z_eq_bool (Fnum x) (- pPred (vNum b))); simpl in |- *.
generalize (Z_eq_bool_correct (- nNormMin radix precision) (pPred (vNum b)));
 case (Z_eq_bool (- nNormMin radix precision) (pPred (vNum b)));
 simpl in |- *.
intros H'; Contradict H'; apply Zlt_not_eq; auto.
rewrite <- (Zopp_involutive (pPred (vNum b))); apply Zlt_Zopp.
apply Zlt_le_trans with (- 0%nat)%Z.
apply Zlt_Zopp; unfold pPred in |- *; apply Zlt_succ_pred; simpl in |- *.
apply (vNumbMoreThanOne radix) with (precision := precision); auto.
simpl in |- *; apply Zlt_le_weak; apply nNormPos; auto with zarith arith.
generalize
 (Z_eq_bool_correct (- nNormMin radix precision) (- nNormMin radix precision));
 case (Z_eq_bool (- nNormMin radix precision) (- nNormMin radix precision));
 simpl in |- *.
generalize (Z_eq_bool_correct (Zsucc (Fexp x)) (- dExp b));
 case (Z_eq_bool (Zsucc (Fexp x)) (- dExp b)); simpl in |- *.
intros H' H'0 H'1 H'2; absurd (- dExp b <= Fexp x)%Z; auto with float.
rewrite <- H'; auto with zarith.
intros H' H'0 H'1 H'2; rewrite <- H'2; apply floatEq; simpl in |- *; auto;
 unfold Zsucc, Zpred in |- *; ring.
intros H'; case H'; auto.
generalize (Z_eq_bool_correct (Fnum x) (nNormMin radix precision));
 case (Z_eq_bool (Fnum x) (nNormMin radix precision)); 
 simpl in |- *.
generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); simpl in |- *.
generalize (Z_eq_bool_correct (Zpred (Fnum x)) (pPred (vNum b)));
 case (Z_eq_bool (Zpred (Fnum x)) (pPred (vNum b))); 
 simpl in |- *.
intros H' H'0 H'1 H'2; absurd (nNormMin radix precision <= pPred (vNum b))%Z;
 auto with float.
rewrite <- H'; rewrite H'1; auto with zarith.
rewrite <- H'1; auto with float.
apply Zle_Zabs_inv2; auto with float zarith.
unfold pPred in |- *; apply Zle_Zpred; auto with float.
generalize (Z_eq_bool_correct (Zpred (Fnum x)) (- nNormMin radix precision));
 case (Z_eq_bool (Zpred (Fnum x)) (- nNormMin radix precision));
 simpl in |- *.
intros H' H'0 H'1 H'2 H'3;
 absurd (Zpred (nNormMin radix precision) = (- nNormMin radix precision)%Z);
 auto with zarith.
intros H' H'0 H'1 H'2 H'3; apply floatEq; simpl in |- *; auto;
 unfold Zpred, Zsucc in |- *; ring.
generalize (Z_eq_bool_correct (pPred (vNum b)) (pPred (vNum b)));
 case (Z_eq_bool (pPred (vNum b)) (pPred (vNum b))); 
 auto.
intros H' H'0 H'1 H'2; rewrite <- H'1; apply floatEq; simpl in |- *; auto;
 unfold Zpred, Zsucc in |- *; ring.
intros H'; case H'; auto.
generalize (Z_eq_bool_correct (Zpred (Fnum x)) (pPred (vNum b)));
 case (Z_eq_bool (Zpred (Fnum x)) (pPred (vNum b))); 
 simpl in |- *.
intros H'; absurd (Fnum x <= pPred (vNum b))%Z; auto with float.
rewrite <- H'.
apply Zlt_not_le; apply Zlt_pred; auto.
apply Zle_Zabs_inv2; unfold pPred in |- *; apply Zle_Zpred; auto with float.
generalize (Z_eq_bool_correct (Zpred (Fnum x)) (- nNormMin radix precision));
 case (Z_eq_bool (Zpred (Fnum x)) (- nNormMin radix precision));
 simpl in |- *.
generalize (Z_eq_bool_correct (Fexp x) (- dExp b));
 case (Z_eq_bool (Fexp x) (- dExp b)); simpl in |- *.
intros H' H'0 H'1 H'2 H'3; apply floatEq; simpl in |- *; auto;
 unfold Zsucc, Zpred in |- *; ring.
intros H' H'0 H'1 H'2 H'3; case H; intros C0.
absurd (nNormMin radix precision <= Zabs (Fnum x))%Z; auto with float.
replace (Fnum x) with (Zsucc (Zpred (Fnum x)));
 [ idtac | unfold Zsucc, Zpred in |- *; ring ].
rewrite H'0.
rewrite <- Zopp_Zpred_Zs; rewrite Zabs_Zopp.
rewrite Zabs_eq; auto with zarith.
apply Zle_Zpred; simpl in |- *; apply nNormPos; auto with float zarith.
apply pNormal_absolu_min with (b := b); auto.
Contradict H'; apply FsubnormalFexp with (1 := C0).
intros H' H'0 H'1 H'2; apply floatEq; simpl in |- *; auto.
unfold Zpred, Zsucc in |- *; ring.
Qed.
 
Theorem FNPredSuc :
 forall x : float,
 Fbounded b x -> FNPred (FNSucc b radix precision x) = x :>R.
intros x H'; unfold FNPred in |- *; rewrite FcanonicFnormalizeEq; auto.
unfold FNSucc in |- *; rewrite FPredSuc; auto.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
apply FnormalizeCanonic; auto.
apply FNSuccCanonic; auto.
Qed.
 
Theorem FNPredSucEq :
 forall x : float,
 Fcanonic radix b x -> FNPred (FNSucc b radix precision x) = x.
intros x H'.
apply FcanonicUnique with (precision := precision) (5 := H'); auto.
apply FNPredCanonic; auto with float.
apply FcanonicBound with (radix := radix); auto.
apply FNSuccCanonic; auto.
apply FcanonicBound with (radix := radix); auto.
apply FNPredSuc; auto.
apply FcanonicBound with (radix := radix); auto.
Qed.
 
Theorem FNSucPred :
 forall x : float,
 Fbounded b x -> FNSucc b radix precision (FNPred x) = x :>R.
intros x H'; unfold FNSucc in |- *; rewrite FcanonicFnormalizeEq; auto.
unfold FNPred in |- *; rewrite FSucPred; auto.
unfold FtoRradix in |- *; apply FnormalizeCorrect; auto.
apply FnormalizeCanonic; auto.
apply FNPredCanonic; auto.
Qed.
 
Theorem FNSucPredEq :
 forall x : float,
 Fcanonic radix b x -> FNSucc b radix precision (FNPred x) = x.
intros x H'.
apply FcanonicUnique with (5 := H') (precision := precision); auto.
apply FNSuccCanonic; auto.
apply FcanonicBound with (radix := radix); auto.
apply FNPredCanonic; auto.
apply FcanonicBound with (radix := radix); auto.
apply FNSucPred; auto.
apply FcanonicBound with (radix := radix); auto.
Qed.


End pred.
Hint Resolve FBoundedPred FPredCanonic FPredLt R0RltRleSucc FPredProp
  FNPredCanonic FNPredLt FNPredProp: float.