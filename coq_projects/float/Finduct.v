(****************************************************************************
                                                                             
          IEEE754  :  Finduct                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  *****************************************************************************
  Define an induction principle on float*)
Require Export FPred.
Section finduct.
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
 
Definition Fweight (p : float) :=
  (Fnum p + Fexp p * Zpower_nat radix precision)%Z.
 
Theorem FweightLt :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q -> (0 <= p)%R -> (p < q)%R -> (Fweight p < Fweight q)%Z.
intros p q H' H'0 H'1 H'2.
cut (Fbounded b p); [ intros Fb1 | apply FcanonicBound with (1 := H') ]; auto.
cut (Fbounded b q); [ intros Fb2 | apply FcanonicBound with (1 := H'0) ];
 auto.
case (FcanonicLtPos _ radixMoreThanOne b precision) with (p := p) (q := q);
 auto with arith; intros Zl1.
unfold Fweight in |- *; simpl in |- *.
replace (Fexp q) with (Fexp q - Fexp p + Fexp p)%Z; [ idtac | ring ].
rewrite Zmult_plus_distr_l.
rewrite Zplus_assoc.
repeat rewrite (fun x y z : Z => Zplus_comm x (y * z)).
apply Zplus_lt_compat_l.
apply Zlt_le_trans with (Zpower_nat radix precision); auto with zarith.
apply Zle_lt_trans with (Zpred (Zpower_nat radix precision));
 auto with zarith.
apply Zle_Zabs_inv2; auto with float zarith.
apply Zle_Zpred; auto with float zarith.
rewrite <- pGivesBound; auto with float.
apply Zle_trans with ((Fexp q - Fexp p) * Zpower_nat radix precision)%Z;
 auto with zarith.
pattern (Zpower_nat radix precision) at 1 in |- *;
 replace (Zpower_nat radix precision) with
  (Zsucc 0 * Zpower_nat radix precision)%Z; auto.
apply Zle_Zmult_comp_r; auto with zarith.
unfold Zsucc in |- *; ring.
cut (0 <= Fnum q)%Z; auto with zarith.
apply (LeR0Fnum radix); auto.
apply Rle_trans with (FtoRradix p); auto; apply Rlt_le; auto.
elim Zl1; intros H'3 H'4; clear Zl1.
unfold Fweight in |- *; simpl in |- *.
rewrite <- H'3.
repeat rewrite (fun x y z : Z => Zplus_comm x (y * z)).
apply Zplus_lt_compat_l; auto.
Qed.
 
Theorem FweightEq :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q -> p = q :>R -> Fweight p = Fweight q.
intros p q H' H'0 H'1.
rewrite
 (FcanonicUnique _ radixMoreThanOne b precision) with (p := p) (q := q);
 auto with arith.
Qed.
 
Theorem FweightZle :
 forall p q : float,
 Fcanonic radix b p ->
 Fcanonic radix b q -> (0 <= p)%R -> (p <= q)%R -> (Fweight p <= Fweight q)%Z.
intros p q H' H'0 H'1 H'2; Casec H'2; intros H'2.
apply Zlt_le_weak.
apply FweightLt; auto.
rewrite (FweightEq p q); auto with zarith.
Qed.
 
Theorem FinductPosAux :
 forall (P : float -> Prop) (p : float),
 (0 <= p)%R ->
 Fcanonic radix b p ->
 P p ->
 (forall q : float,
  Fcanonic radix b q -> (p <= q)%R -> P q -> P (FSucc b radix precision q)) ->
 forall x : Z,
 (0 <= x)%Z ->
 forall q : float,
 x = (Fweight q - Fweight p)%Z -> Fcanonic radix b q -> (p <= q)%R -> P q.
intros P p H' H'0 H'1 H'2 x H'3; pattern x in |- *.
apply Z_lt_induction; auto.
intros x0 H'4 q H'5 H'6 H'7.
Casec H'7; intros H'7.
cut (p <= FPred b radix precision q)%R; [ intros Rl1 | idtac ].
cut (P (FPred b radix precision q)); [ intros P1 | idtac ].
rewrite <- (FSucPred b radix precision) with (x := q); auto with arith.
apply H'2; auto with float arith.
apply H'4 with (y := (Fweight (FPred b radix precision q) - Fweight p)%Z);
 auto.
split.
cut (Fweight p <= Fweight (FPred b radix precision q))%Z; auto with zarith.
apply FweightZle; auto.
apply FPredCanonic; auto with arith.
rewrite H'5.
cut (Fweight (FPred b radix precision q) < Fweight q)%Z;
 [ auto with zarith | idtac ].
apply FweightLt; auto with float.
apply (R0RltRlePred b radix precision); auto.
apply Rle_lt_trans with (FtoRradix p); auto.
apply (FPredLt b radix precision); auto.
apply (FPredCanonic b radix precision); auto with arith.
apply (FPredProp b radix precision); auto with arith.
rewrite <-
 (FcanonicUnique _ radixMoreThanOne b precision) with (p := p) (q := q);
 auto with arith.
Qed.
 
Theorem FinductPos :
 forall (P : float -> Prop) (p : float),
 (0 <= p)%R ->
 Fcanonic radix b p ->
 P p ->
 (forall q : float,
  Fcanonic radix b q -> (p <= q)%R -> P q -> P (FSucc b radix precision q)) ->
 forall q : float, Fcanonic radix b q -> (p <= q)%R -> P q.
intros P p H' H'0 H'1 H'2 q H'3 H'4.
apply FinductPosAux with (p := p) (x := (Fweight q - Fweight p)%Z); auto.
cut (Fweight p <= Fweight q)%Z; [ auto with zarith | idtac ].
apply FweightZle; auto with float.
Qed.
 
Theorem FinductNegAux :
 forall (P : float -> Prop) (p : float),
 (0 <= p)%R ->
 Fcanonic radix b p ->
 P p ->
 (forall q : float,
  Fcanonic radix b q ->
  (0 < q)%R -> (q <= p)%R -> P q -> P (FPred b radix precision q)) ->
 forall x : Z,
 (0 <= x)%Z ->
 forall q : float,
 x = (Fweight p - Fweight q)%Z ->
 Fcanonic radix b q -> (0 <= q)%R -> (q <= p)%R -> P q.
intros P p H' H'0 H'1 H'2 x H'3; pattern x in |- *.
apply Z_lt_induction; auto.
intros x0 H'4 q H'5 H'6 H'7 H'8.
Casec H'8; intros H'8.
cut (FSucc b radix precision q <= p)%R; [ intros Rle1 | idtac ].
cut (P (FSucc b radix precision q)); [ intros P1 | idtac ].
rewrite <- (FPredSuc b radix precision) with (x := q); auto with arith.
apply H'2; auto with float arith.
apply Rle_lt_trans with (FtoRradix q); auto.
apply (FSuccLt b radix); auto with arith.
apply H'4 with (y := (Fweight p - Fweight (FSucc b radix precision q))%Z);
 auto.
split.
cut (Fweight (FSucc b radix precision q) <= Fweight p)%Z; auto with zarith.
apply FweightZle; auto.
apply FSuccCanonic; auto with arith.
apply Rle_trans with (FtoRradix q); auto; apply Rlt_le.
apply (FSuccLt b radix); auto with arith.
rewrite H'5.
cut (Fweight q < Fweight (FSucc b radix precision q))%Z;
 [ auto with zarith | idtac ].
apply FweightLt; auto with float.
apply (FSuccLt b radix); auto with arith.
apply FSuccCanonic; auto with arith.
apply Rle_trans with (FtoRradix q); auto; apply Rlt_le.
apply (FSuccLt b radix); auto with arith.
apply (FSuccProp b radix); auto with arith.
rewrite <-
 (FcanonicUnique _ radixMoreThanOne b precision) with (p := p) (q := q);
 auto with arith.
Qed.
 
Theorem FinductNeg :
 forall (P : float -> Prop) (p : float),
 (0 <= p)%R ->
 Fcanonic radix b p ->
 P p ->
 (forall q : float,
  Fcanonic radix b q ->
  (0 < q)%R -> (q <= p)%R -> P q -> P (FPred b radix precision q)) ->
 forall q : float, Fcanonic radix b q -> (0 <= q)%R -> (q <= p)%R -> P q.
intros P p H' H'0 H'1 H'2 q H'3 H'4 H'5.
apply FinductNegAux with (p := p) (x := (Fweight p - Fweight q)%Z); auto.
cut (Fweight q <= Fweight p)%Z; [ auto with zarith | idtac ].
apply FweightZle; auto with float.
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
case H'; intros H1 H2; red in H1.
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
rewrite Zabs_eq; auto with zarith.
apply ZltNormMinVnum; auto with zarith.
unfold nNormMin in |- *; auto with zarith.
apply Zle_trans with (Fexp p); auto with float zarith.
case H'; auto with float.
rewrite <- (PosNormMin radix b precision); auto with zarith.
apply Rle_trans with (1 := H'1); auto with real.
apply Rlt_trans with (1 := H'3).
unfold FtoR in |- *; simpl in |- *.
rewrite powerRZ_Zs; auto with real zarith; auto.
rewrite <- Rmult_assoc;
 rewrite (fun (x : R) (y : Z) => Rmult_comm x y); 
 rewrite Rmult_assoc; auto.
apply Rmult_lt_compat_l; auto with real arith.
case H'.
intros H'5 H'6; elim H'6; intros H'7 H'8; rewrite H'7; clear H'6.
change (p < firstNormalPos radix b precision)%R in |- *.
apply (FsubnormalLtFirstNormalPos radix); auto with arith.
simpl in |- *; intros; apply Zle_antisym; auto with zarith.
intros H'5; elim H'5; intros H'6 H'7; rewrite H'6; clear H'5; auto.
Qed.
End finduct.