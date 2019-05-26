(****************************************************************************
                                                                             
          IEEE754  :  Fround                                                     
                                                                             
          Laurent Thery                                                      
                                                                             
  ******************************************************************************)
Require Export Fprop.
Require Export Fodd.
Section FRound.
Variable b : Fbound.
Variable radix : Z.
Variable precision : nat.
 
Let FtoRradix := FtoR radix.
Local Coercion FtoRradix : float >-> R.

Hypothesis radixMoreThanOne : (1 < radix)%Z.
Hypothesis precisionGreaterThanOne : 1 < precision.
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix precision.
 
Definition TotalP (P : R -> float -> Prop) :=
  forall r : R, exists p : float, P r p.
 
Definition UniqueP (P : R -> float -> Prop) :=
  forall (r : R) (p q : float), P r p -> P r q -> p = q :>R.
 
Definition CompatibleP (P : R -> float -> Prop) :=
  forall (r1 r2 : R) (p q : float),
  P r1 p -> r1 = r2 -> p = q :>R -> Fbounded b q -> P r2 q.
 
Definition MinOrMaxP (P : R -> float -> Prop) :=
  forall (r : R) (p : float), P r p -> isMin b radix r p \/ isMax b radix r p.
 
Definition RoundedModeP (P : R -> float -> Prop) :=
  TotalP P /\ CompatibleP P /\ MinOrMaxP P /\ MonotoneP radix P.
 
Theorem RoundedModeP_inv1 : forall P, RoundedModeP P -> TotalP P.
intros P H; case H; auto.
Qed.
 
Theorem RoundedModeP_inv2 : forall P, RoundedModeP P -> CompatibleP P.
intros P H; Casec H; intros H H1; Casec H1; auto.
Qed.
 
Theorem RoundedModeP_inv3 : forall P, RoundedModeP P -> MinOrMaxP P.
intros P H; Casec H; intros H H1; Casec H1; intros H1 H2; Casec H2; auto.
Qed.
 
Theorem RoundedModeP_inv4 : forall P, RoundedModeP P -> MonotoneP radix P.
intros P H; Casec H; intros H H1; Casec H1; intros H1 H2; Casec H2; auto.
Qed.
Hint Resolve RoundedModeP_inv1 RoundedModeP_inv2 RoundedModeP_inv3
  RoundedModeP_inv4: inv.
 
Theorem RoundedProjector : forall P, RoundedModeP P -> ProjectorP b radix P.
intros P H'; red in |- *; simpl in |- *.
intros p q H'0 H'1.
red in H'.
elim H'; intros H'2 H'3; elim H'3; intros H'4 H'5; elim H'5; intros H'6 H'7;
 case (H'6 p q); clear H'5 H'3 H'; auto.
intros H'; apply (ProjectMin b radix p); auto.
intros H'; apply (ProjectMax b radix p); auto.
Qed.
 
Theorem MinCompatible : CompatibleP (isMin b radix).
red in |- *.
intros r1 r2 p q H' H'0 H'1 H'2; split; auto.
rewrite <- H'0; unfold FtoRradix in H'1; rewrite <- H'1; case H'; auto.
Qed.
 
Theorem MinRoundedModeP : RoundedModeP (isMin b radix).
split; try red in |- *.
intros r; apply MinEx with (precision := precision); auto with arith.
split; try exact MinCompatible.
split; try apply MonotoneMin; red in |- *; auto.
Qed.
 
Theorem MaxCompatible : CompatibleP (isMax b radix).
red in |- *.
intros r1 r2 p q H' H'0 H'1 H'2; split; auto.
rewrite <- H'0; unfold FtoRradix in H'1; rewrite <- H'1; case H'; auto.
Qed.
 
Theorem MaxRoundedModeP : RoundedModeP (isMax b radix).
split; try red in |- *.
intros r; apply MaxEx with (precision := precision); auto with arith.
split; try exact MaxCompatible.
split; try apply MonotoneMax; red in |- *; auto.
Qed.
 
Definition ToZeroP (r : R) (p : float) :=
  (0 <= r)%R /\ isMin b radix r p \/ (r <= 0)%R /\ isMax b radix r p.
 
Theorem ToZeroTotal : TotalP ToZeroP.
red in |- *; intros r; case (Rle_or_lt r 0); intros H1.
case MaxEx with (r := r) (3 := pGivesBound); auto with arith.
intros x H'; exists x; red in |- *; auto.
case MinEx with (r := r) (3 := pGivesBound); auto with arith.
intros x H'; exists x; red in |- *; left; split; auto.
apply Rlt_le; auto.
Qed.
 
Theorem ToZeroCompatible : CompatibleP ToZeroP.
red in |- *.
intros r1 r2 p q H'; case H'.
intros H'0 H'1 H'2; left; split;
 try apply MinCompatible with (p := p) (r1 := r1); 
 try rewrite <- H'1; auto; case H'0; auto.
intros H'0 H'1 H'2; right; split;
 try apply MaxCompatible with (p := p) (r1 := r1); 
 try rewrite <- H'1; auto; case H'0; auto.
Qed.
 
Theorem ToZeroMinOrMax : MinOrMaxP ToZeroP.
red in |- *.
intros r p H'; case H'; clear H'; intros H'; case H'; auto.
Qed.
 
Theorem ToZeroMonotone : MonotoneP radix ToZeroP.
red in |- *.
cut (FtoR radix (Fzero (- dExp b)) = 0%R);
 [ intros Eq0 | unfold FtoR in |- *; simpl in |- * ]; 
 auto with real.
simpl in |- *; intros p q p' q' H' H'0; case H'0; clear H'0.
intros H'0; elim H'0; intros H'1 H'2; clear H'0; intros H'0.
case H'0; intros H'3; elim H'3; clear H'3; auto.
intros H'3 H'4.
apply (MonotoneMin b radix) with (p := p) (q := q); auto.
intros H'3 H'4.
apply Rle_trans with p; [ apply isMin_inv1 with (1 := H'2); auto | idtac ].
apply Rle_trans with q; [ idtac | apply isMax_inv1 with (1 := H'4) ]; auto.
apply Rlt_le; auto.
intros H'0; elim H'0; intros H'1 H'2; clear H'0.
intros H'0; case H'0; clear H'0; intros H'0; case H'0; intros H'3 H'4;
 clear H'0.
apply Rle_trans with (FtoRradix (Fzero (- dExp b))); auto.
elim H'2.
intros H'0 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
repeat split; simpl in |- *; auto with zarith.
rewrite Eq0; auto.
elim H'4.
intros H'0 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
repeat split; simpl in |- *; auto with zarith.
rewrite Eq0; auto.
apply (MonotoneMax b radix) with (p := p) (q := q); auto.
Qed.
 
Theorem ToZeroRoundedModeP : RoundedModeP ToZeroP.
repeat split.
try exact ToZeroTotal.
try exact ToZeroCompatible.
try exact ToZeroMinOrMax.
try exact ToZeroMonotone.
Qed.
 
Definition ToInfinityP (r : R) (p : float) :=
  (r <= 0)%R /\ isMin b radix r p \/ (0 <= r)%R /\ isMax b radix r p.
 
Theorem ToInfinityTotal : TotalP ToInfinityP.
red in |- *; intros r; case (Rle_or_lt r 0); intros H1.
case MinEx with (r := r) (3 := pGivesBound); auto with arith.
intros x H'; exists x; red in |- *; auto.
case MaxEx with (r := r) (3 := pGivesBound); auto with arith.
intros x H'; exists x; red in |- *; right; split; auto.
apply Rlt_le; auto.
Qed.
 
Theorem ToInfinityCompatible : CompatibleP ToInfinityP.
red in |- *.
intros r1 r2 p q H'; case H'.
intros H'0 H'1 H'2; left; split;
 try apply MinCompatible with (p := p) (r1 := r1); 
 try rewrite <- H'1; case H'0; auto.
intros H'0 H'1 H'2; right; split;
 try apply MaxCompatible with (p := p) (r1 := r1); 
 try rewrite <- H'1; case H'0; auto.
Qed.
 
Theorem ToInfinityMinOrMax : MinOrMaxP ToInfinityP.
red in |- *.
intros r p H'; case H'; clear H'; intros H'; case H'; auto.
Qed.
 
Theorem ToInfinityMonotone : MonotoneP radix ToInfinityP.
red in |- *; simpl in |- *.
cut (FtoR radix (Fzero (- dExp b)) = 0%R);
 [ intros Eq0 | unfold FtoR in |- *; simpl in |- * ]; 
 auto with real.
intros p q p' q' H' H'0; case H'0; clear H'0.
intros H'0; elim H'0; intros H'1 H'2; clear H'0; intros H'0.
case H'0; intros H'3; elim H'3; clear H'3; auto.
intros H'3 H'4.
apply (MonotoneMin b radix) with (p := p) (q := q); auto.
intros H'3 H'4.
apply Rle_trans with p; [ apply isMin_inv1 with (1 := H'2); auto | idtac ].
apply Rle_trans with q; [ auto | apply isMax_inv1 with (1 := H'4) ]; auto.
apply Rlt_le; auto.
intros H'0; elim H'0; intros H'1 H'2; clear H'0.
intros H'0; case H'0; clear H'0; intros H'0; case H'0; intros H'3 H'4;
 clear H'0.
2: apply (MonotoneMax b radix) with (p := p) (q := q); auto.
apply Rle_trans with (FtoRradix (Fzero (- dExp b))); auto.
elim H'2.
intros H'0 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
repeat split; simpl in |- *; auto with zarith.
apply Rle_trans with q; auto.
apply Rlt_le; auto.
rewrite Eq0; auto.
elim H'4.
intros H'0 H'5; elim H'5; intros H'6 H'7; apply H'7; clear H'5; auto.
repeat split; simpl in |- *; auto with zarith.
apply Rle_trans with p; auto.
rewrite Eq0; auto.
apply Rlt_le; auto.
Qed.
 
Theorem ToInfinityRoundedModeP : RoundedModeP ToInfinityP.
repeat split.
try exact ToInfinityTotal.
try exact ToInfinityCompatible.
try exact ToInfinityMinOrMax.
try exact ToInfinityMonotone.
Qed.
 
Theorem MinUniqueP : UniqueP (isMin b radix).
red in |- *.
intros r p q H' H'0.
unfold FtoRradix in |- *; apply MinEq with (1 := H'); auto.
Qed.
 
Theorem MaxUniqueP : UniqueP (isMax b radix).
red in |- *.
intros r p q H' H'0.
unfold FtoRradix in |- *; apply MaxEq with (1 := H'); auto.
Qed.
 
Theorem ToZeroUniqueP : UniqueP ToZeroP.
red in |- *.
intros r p q H' H'0.
inversion H'; inversion H'0; elim H0; elim H; clear H0 H;
 intros H'1 H'2 H'3 H'4.
apply (MinUniqueP r); auto.
cut (r = Fzero (- dExp b) :>R);
 [ intros Eq0
 | apply Rle_antisym; unfold FtoRradix, Fzero, FtoR in |- *; simpl in |- * ];
 try rewrite Rmult_0_l; auto with real.
apply trans_eq with (FtoRradix (Fzero (- dExp b))).
apply sym_eq; unfold FtoRradix in |- *;
 apply (RoundedProjector _ ToZeroRoundedModeP); auto with float.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
unfold FtoRradix in |- *; apply (RoundedProjector _ ToZeroRoundedModeP);
 auto with float.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
cut (r = Fzero (- dExp b) :>R);
 [ intros Eq0
 | apply Rle_antisym; unfold FtoRradix, Fzero, FtoR in |- *; simpl in |- * ];
 try rewrite Rmult_0_l; auto with real.
apply trans_eq with (FtoRradix (Fzero (- dExp b))).
apply sym_eq; unfold FtoRradix in |- *;
 apply (RoundedProjector _ ToZeroRoundedModeP); auto with float.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
unfold FtoRradix in |- *; apply (RoundedProjector _ ToZeroRoundedModeP);
 auto with float.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
apply (MaxUniqueP r); auto.
Qed.
 
Theorem ToInfinityUniqueP : UniqueP ToInfinityP.
red in |- *.
intros r p q H' H'0.
inversion H'; inversion H'0; elim H0; elim H; clear H0 H;
 intros H'1 H'2 H'3 H'4.
apply (MinUniqueP r); auto.
cut (r = Fzero (- dExp b) :>R);
 [ intros Eq0
 | apply Rle_antisym; unfold FtoRradix, Fzero, FtoR in |- *; simpl in |- * ];
 try rewrite Rmult_0_l; auto with real.
apply trans_eq with (FtoRradix (Fzero (- dExp b))).
apply sym_eq; unfold FtoRradix in |- *;
 apply (RoundedProjector _ ToInfinityRoundedModeP); 
 auto.
apply FboundedFzero; auto.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
unfold FtoRradix in |- *; apply (RoundedProjector _ ToInfinityRoundedModeP);
 auto.
apply FboundedFzero; auto.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
cut (r = Fzero (- dExp b) :>R);
 [ intros Eq0
 | apply Rle_antisym; unfold FtoRradix, Fzero, FtoR in |- *; simpl in |- * ];
 try rewrite Rmult_0_l; auto with float.
apply trans_eq with (FtoRradix (Fzero (- dExp b))).
apply sym_eq; unfold FtoRradix in |- *;
 apply (RoundedProjector _ ToInfinityRoundedModeP); 
 auto.
apply FboundedFzero; auto.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
unfold FtoRradix in |- *; apply (RoundedProjector _ ToInfinityRoundedModeP);
 auto.
apply FboundedFzero; auto.
unfold FtoRradix in Eq0; rewrite <- Eq0; auto.
apply (MaxUniqueP r); auto.
Qed.
 
 
Theorem MinOrMaxRep :
 forall P,
 MinOrMaxP P ->
 forall p q : float, P p q -> exists m : Z, q = Float m (Fexp p) :>R.
intros P H' p q H'0; case (H' p q); auto; intros H'1.
apply FminRep with (3 := pGivesBound); auto with arith.
apply FmaxRep with (3 := pGivesBound); auto with arith.
Qed.
 
Theorem RoundedModeRep :
 forall P,
 RoundedModeP P ->
 forall p q : float, P p q -> exists m : Z, q = Float m (Fexp p) :>R.
intros P H' p q H'0.
apply MinOrMaxRep with (P := P); auto with inv.
Qed.
 
Definition SymmetricP (P : R -> float -> Prop) :=
  forall (r : R) (p : float), P r p -> P (- r)%R (Fopp p).
 
Theorem ToZeroSymmetric : SymmetricP ToZeroP.
red in |- *; intros r p H'; case H'; clear H'; intros H'; case H';
 intros H'1 H'2.
right; split; auto.
replace 0%R with (-0)%R; auto with real.
apply MinOppMax; auto.
left; split; auto.
replace 0%R with (-0)%R; auto with real.
apply MaxOppMin; auto.
Qed.
 
Theorem ToInfinitySymmetric : SymmetricP ToInfinityP.
red in |- *; intros r p H'; case H'; clear H'; intros H'; case H';
 intros H'1 H'2.
right; split; auto.
replace 0%R with (-0)%R; auto with real.
apply MinOppMax; auto.
left; split; auto.
replace 0%R with (-0)%R; auto with real.
apply MaxOppMin; auto.
Qed.
 
Theorem ScalableRoundedModeP :
 forall P (f s t : float),
 RoundedModeP P ->
 Fbounded b f -> P (radix * f)%R s -> P (s / radix)%R t -> f = t :>R.
intros P f s t HP Ff H1 H2.
cut (ProjectorP b radix P);
 [ unfold ProjectorP in |- *; intros HP2 | apply RoundedProjector; auto ].
cut (FtoR radix (Float (Fnum f) (Zsucc (Fexp f))) = (radix * FtoR radix f)%R);
 [ intros V | idtac].
2: unfold FtoR, Zsucc in |- *; simpl in |- *; ring_simplify.
2: rewrite powerRZ_add; [ simpl in |- *; ring | auto with zarith real ].
unfold FtoRradix in |- *; apply HP2; auto.
replace (FtoR radix f) with (FtoR radix s / radix)%R; auto.
replace (FtoR radix s) with (radix * FtoR radix f)%R;
 [ unfold Rdiv in |- * | rewrite <- V ].
rewrite Rmult_comm; rewrite <- Rmult_assoc; rewrite Rinv_l;
 auto with real zarith.
apply HP2; auto with float.
repeat (split; simpl in |- *; auto with zarith float).
rewrite V; auto.
Qed.
 
Theorem RoundLessThanIsMax :
 forall P,
 RoundedModeP P ->
 forall (p m : float) (x : R), P x p -> isMax b radix x m -> (p <= m)%R.
intros.
elim H; intros.
elim H3; intros H' H'0; clear H3.
elim H'0; intros; clear H'0.
case (H3 x p); auto.
intros; apply Rle_trans with x; auto.
elim H5; intros; elim H7; intros; auto with real.
elim H1; intros; elim H7; intros; auto with real.
intros; replace (FtoRradix p) with (FtoRradix m); auto with real.
unfold FtoRradix in |- *; apply MaxEq with b x; auto.
Qed.
End FRound.
Hint Resolve RoundedProjector MinCompatible MinRoundedModeP MaxCompatible
  MaxRoundedModeP ToZeroTotal ToZeroCompatible ToZeroMinOrMax ToZeroMonotone
  ToZeroRoundedModeP ToInfinityTotal ToInfinityCompatible ToInfinityMinOrMax
  ToInfinityMonotone ToInfinityRoundedModeP MinUniqueP MaxUniqueP
  ToZeroUniqueP ToInfinityUniqueP FnOddNEven ToZeroSymmetric
  ToInfinitySymmetric: float.
Hint Resolve RoundedModeP_inv1 RoundedModeP_inv2 RoundedModeP_inv3
  RoundedModeP_inv4: inv.