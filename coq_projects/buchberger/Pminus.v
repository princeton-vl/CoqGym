(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export Pmults.
Require Import Arith.
Section Pminus.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hMults".
 
Inductive minusP :
list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop :=
  | mnillu1 :
      forall l1 : list (Term A n),
      minusP (pO A n) l1
        (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l1)
  | mnillu2 : forall l1 : list (Term A n), minusP l1 (pO A n) l1
  | mmainu1 :
      forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)),
      ltT ltM a2 a1 ->
      minusP l1 (pX a2 l2) l3 -> minusP (pX a1 l1) (pX a2 l2) (pX a1 l3)
  | mmainu2a :
      forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)),
      minusP l1 l2 l3 ->
      eqT a1 a2 ->
      zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a1 a2) ->
      minusP (pX a1 l1) (pX a2 l2) l3
  | mmainu2b :
      forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)),
      minusP l1 l2 l3 ->
      eqT a1 a2 ->
      ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a1 a2) ->
      minusP (pX a1 l1) (pX a2 l2)
        (pX (minusTerm (A:=A) minusA (n:=n) a1 a2) l3)
  | mmainu3 :
      forall (a1 a2 : Term A n) (l1 l2 l3 : list (Term A n)),
      ltT ltM a1 a2 ->
      minusP (pX a1 l1) l2 l3 ->
      minusP (pX a1 l1) (pX a2 l2) (pX (invTerm (A:=A) invA (n:=n) a2) l3).
Hint Resolve mnillu1 mnillu2 mmainu1 mmainu2a mmainu2b mmainu3.
Require Import LetP.
 
Definition minuspp :
  forall l : list (Term A n) * list (Term A n),
  {a : list (Term A n) | minusP (fst l) (snd l) a}.
intros l; pattern l in |- *.
apply
 well_founded_induction
  with (A := (list (Term A n) * list (Term A n))%type) (R := lessP A n); 
 auto.
apply wf_lessP; auto.
intros x; case x; intros l1 l2; simpl in |- *.
case l1.
intros H';
 exists (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2);
 auto.
intros a1 m1; case l2.
intros H'; exists (pX a1 m1); auto.
intros a2 m2 H'; case (ltT_dec A n ltM ltM_dec a1 a2);
 [ intros P; case P; clear P | idtac ]; intros H1.
lapply (H' (pX a1 m1, m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX (invTerm (A:=A) invA (n:=n) a2) Orec); auto.
change
  (minusP (pX a1 m1) (pX a2 m2) (pX (invTerm (A:=A) invA (n:=n) a2) Orec))
 in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
lapply (H' (m1, pX a2 m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX a1 Orec); auto.
change (minusP (pX a1 m1) (pX a2 m2) (pX a1 Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
lapply (H' (m1, m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
apply LetP with (A := Term A n) (h := minusTerm (A:=A) minusA (n:=n) a1 a2).
intros u H'0; case (zeroP_dec A A0 eqA eqA_dec n u); intros Z0.
exists Orec; auto.
rewrite H'0 in Z0; auto.
change (minusP (pX a1 m1) (pX a2 m2) Orec) in |- *; auto.
exists (pX u Orec); auto.
rewrite H'0 in Z0; auto.
rewrite H'0; auto.
change
  (minusP (pX a1 m1) (pX a2 m2)
     (pX (minusTerm (A:=A) minusA (n:=n) a1 a2) Orec)) 
 in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
Defined.
 
Definition minuspf (l1 l2 : list (Term A n)) :=
  projsig1 (list (Term A n)) _ (minuspp (l1, l2)).
 
Theorem zerop_is_eqTerm :
 forall a b : Term A n,
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 eqTerm (A:=A) eqA (n:=n) a b.
intros a b H' H'0.
cut (eqT a (invTerm (A:=A) invA (n:=n) b)); [ intros eq1 | idtac ].
cut (eqT a (plusTerm (A:=A) plusA (n:=n) b (invTerm (A:=A) invA (n:=n) b)));
 [ intros eq2 | idtac ].
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a
            (plusTerm (A:=A) plusA (n:=n) b (invTerm (A:=A) invA (n:=n) b)));
 auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply plusTerm_invTerm_zeroP with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a
            (plusTerm (A:=A) plusA (n:=n) (invTerm (A:=A) invA (n:=n) b) b));
 auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqT_trans A n) with (plusTerm plusA b (invTerm invA b)); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply plusTerm_com with (1 := cs); auto.
apply plusTerm_com with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n)
            (plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b)) b);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply plusTerm_assoc with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply zeroP_plusTerml with (1 := cs); auto.
apply (eqT_trans A n) with (invTerm invA b); auto.
apply plusTerm_eqT2; auto.
apply (eqT_sym A n); apply invTerm_eqT; auto.
apply zeroP_comp_eqTerm with (1 := cs) (2 := H'0).
apply eqTerm_minusTerm_plusTerm_invTerm with (1 := cs); auto.
apply (eqT_trans A n) with (1 := eq1); auto.
apply (eqT_sym A n); apply plusTerm_eqT2; auto.
apply (eqT_trans A n) with (1 := H'); auto.
Qed.
Hint Unfold minuspf.
 
Theorem minusTerm_zeroP_r :
 forall a b : Term A n,
 zeroP (A:=A) A0 eqA (n:=n) a ->
 eqT a b ->
 eqTerm (A:=A) eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b)
   (invTerm (A:=A) invA (n:=n) b).
intros a b H' H0;
 apply
  (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
   with (y := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply zeroP_plusTerml with (1 := cs); auto.
apply (eqT_trans A n) with (y := b); auto.
Qed.
 
Theorem minusTerm_zeroP :
 forall a b : Term A n,
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) b ->
 eqTerm (A:=A) eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) a.
intros a b H' H'0.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) b));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply (eqT_trans A n) with (y := b); auto.
apply zeroP_invTerm_zeroP with (1 := cs); auto.
Qed.
Hint Resolve minusTerm_zeroP minusTerm_zeroP_r.
 
Theorem minusP_pO_is_eqP :
 forall p q r : list (Term A n),
 minusP p q r -> eqP A eqA n r (pO A n) -> eqP A eqA n p q.
intros p q r H'; elim H'; auto.
intros l1; case l1; simpl in |- *; auto.
intros t l H; inversion H.
intros a1 a2 l1 l2 l3 H H0 H1 H2; inversion H2.
intros a1 a2 l1 l2 l3 H H0 H1 H2 H3.
apply eqpP1; auto.
apply zerop_is_eqTerm; auto.
intros a1 a2 l1 l2 l3 H H0 H1 H2 H3; inversion H3.
intros a1 a2 l1 l2 l3 H H0 H1 H2; inversion H2.
Qed.
 
Lemma minusP_inv :
 forall (p q l : list (Term A n)) (a b : Term A n),
 minusP (pX a p) (pX b q) l ->
 exists l1 : list (Term A n),
   ltT ltM b a /\ minusP p (pX b q) l1 /\ l = pX a l1 \/
   ltT ltM a b /\
   minusP (pX a p) q l1 /\ l = pX (invTerm (A:=A) invA (n:=n) b) l1 \/
   eqT a b /\
   (zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) /\
    minusP p q l \/
    ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) /\
    minusP p q l1 /\ l = pX (minusTerm (A:=A) minusA (n:=n) a b) l1).
intros p q l a b H'; simple inversion H'.
discriminate H.
discriminate H0.
rewrite <- H3; rewrite (pX_invl A n a2 b l2 q H2);
 rewrite (pX_invr A n l2 q a2 b H2); rewrite (pX_invl A n a1 a l1 p H1);
 rewrite (pX_invr A n l1 p a1 a H1).
intros H'0 H'1; exists l3; left; split; [ idtac | split ]; auto.
rewrite <- H4.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- (pX_invl A n a2 b l2 q); try rewrite <- (pX_invl A n a1 a l1 p);
 auto.
rewrite <- (pX_invr A n l2 q a2 b); try rewrite <- (pX_invr A n l1 p a1 a);
 auto.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- H4.
rewrite <- (pX_invl A n a2 b l2 q); try rewrite <- (pX_invl A n a1 a l1 p);
 auto.
rewrite <- (pX_invr A n l2 q a2 b); try rewrite <- (pX_invr A n l1 p a1 a);
 auto.
intros H'0 H'1; exists l3; right; left.
rewrite <- (pX_invl A n a2 b l2 q); try rewrite <- (pX_invl A n a1 a l1 p);
 auto.
rewrite <- (pX_invr A n l2 q a2 b); try rewrite <- (pX_invr A n l1 p a1 a);
 auto.
Qed.
 
Theorem uniq_minusp :
 forall (l : list (Term A n) * list (Term A n)) (l3 l4 : list (Term A n)),
 minusP (fst l) (snd l) l3 -> minusP (fst l) (snd l) l4 -> l3 = l4.
unfold pX, pX in |- *.
intros l; pattern l in |- *.
apply well_founded_ind with (1 := wf_lessP A n).
intros (l1, l2); simpl in |- *.
case l1; clear l1.
intros H' l3 l4 H'0; inversion_clear H'0; intros H'2; inversion_clear H'2;
 auto.
case l2; clear l2.
simpl in |- *; intros n0 l0 H' l3 l4 H'0 H'2.
inversion H'2; inversion H'0; auto.
simpl in |- *; intros n2 l2 n1 l1 Induc l3 l4 Hl3 Hl4.
case (minusP_inv l1 l2 l4 n1 n2); auto.
intros x H'; elim H'; intros H'0; [ idtac | elim H'0; clear H'0; intros H'0 ];
 clear H';
 (case (minusP_inv l1 l2 l3 n1 n2); auto; intros x1 H'; elim H'; intros H'1;
   [ idtac | elim H'1; clear H'1; intros H'1 ]; clear H').
elim H'1; intros H' H'2; elim H'2; intros H'3 H'4; rewrite H'4; clear H'2 H'1.
elim H'0; intros H'1 H'2; elim H'2; intros H'5 H'6; rewrite H'6;
 clear H'2 H'0.
apply pX_inj; auto.
apply Induc with (y := (l1, pX n2 l2)); auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (ltT ltM n1 n2); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n2 n1); auto.
apply (eqT_sym A n); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (ltT ltM n1 n2); auto.
elim H'1; intros H' H'2; elim H'2; intros H'3 H'4; rewrite H'4; clear H'2 H'1.
elim H'0; intros H'1 H'2; elim H'2; intros H'5 H'6; rewrite H'6;
 clear H'2 H'0.
apply pX_inj; auto.
apply Induc with (y := (pX n1 l1, l2)); auto; red in |- *; simpl in |- *;
 auto.
rewrite <- plus_n_Sm; auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n1 n2); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n2 n1); auto.
apply (eqT_sym A n); auto.
elim H'1; intros H' H'2; clear H'1.
elim H'0; intros H'1 H'3; clear H'0.
absurd (eqT n1 n2); auto.
elim H'1; intros H' H'2; elim H'2;
 [ intros H'3; clear H'2 H'1
 | intros H'3; elim H'3; intros H'4 H'5; elim H'5; intros H'6 H'7;
    rewrite H'7; clear H'5 H'3 H'2 H'1 ].
elim H'0; intros H'1 H'2; elim H'2;
 [ intros H'4; clear H'2 H'0
 | intros H'4; elim H'4; intros H'5 H'6; apply H'5 || elim H'5;
    try assumption; clear H'4 H'2 H'0 ].
elim H'4; intros H'0 H'2; clear H'4.
elim H'3; intros H'4 H'5; clear H'3.
apply Induc with (y := (l1, l2)); auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
elim H'3; intros H'0 H'2; clear H'3; auto.
elim H'0; intros H'1 H'2; elim H'2;
 [ intros H'3; clear H'2 H'0
 | intros H'3; elim H'3; intros H'5 H'8; elim H'8; intros H'9 H'10;
    rewrite H'10; clear H'8 H'3 H'2 H'0 ].
elim H'3; intros H'0 H'2; clear H'3.
apply H'4 || elim H'4; auto.
apply pX_inj; auto.
apply Induc with (y := (l1, l2)); auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
Qed.
 
Theorem minuspf_is_minusP :
 forall l1 l2 : list (Term A n), minusP l1 l2 (minuspf l1 l2).
intros l1 l2; try assumption.
unfold minuspf in |- *; case (minuspp (pair l1 l2)); simpl in |- *; auto.
Qed.
Hint Resolve minuspf_is_minusP.
 
Theorem minuspf_pO_is_eqP :
 forall p q : list (Term A n),
 eqP A eqA n (minuspf p q) (pO A n) -> eqP A eqA n p q.
intros p q H'.
apply minusP_pO_is_eqP with (r := minuspf p q); auto.
Qed.
 
Theorem order_minusP :
 forall (l1 l2 l3 : list (Term A n)) (a : Term A n),
 minusP l1 l2 l3 ->
 canonical A0 eqA ltM (pX a l1) ->
 canonical A0 eqA ltM (pX a l2) ->
 canonical A0 eqA ltM l3 -> canonical A0 eqA ltM (pX a l3).
intros l1 l2 l3 a H'; elim H'; auto.
intros l4 H'0 H'1 H'2.
cut (canonical A0 eqA ltM l4);
 try apply canonical_imp_canonical with (a := a); auto; 
 intros C0.
apply
 canonical_pX_eqT
  with
    (a := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            a); auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
        (pX a l4))) in |- *; auto.
apply (eqT_sym A n);
 apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a);
 auto.
apply (T1_eqT A A1 eqA); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply canonical_cons; auto.
apply (canonical_pX_order A A0 eqA) with (ltM := ltM) (l := l4); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pX a1 l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5 H'6.
apply H'1; auto.
apply canonical_skip_fst with (b := a1); auto.
apply canonical_skip_fst with (b := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5 H'6.
apply canonical_cons; auto.
apply minusTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l4); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pX a1 l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply canonical_cons; auto.
apply invTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l5); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pX a1 l4); auto.
Qed.
 
Theorem canonical_minusP :
 forall l1 l2 l3 : list (Term A n),
 minusP l1 l2 l3 ->
 canonical A0 eqA ltM l1 ->
 canonical A0 eqA ltM l2 -> canonical A0 eqA ltM l3.
intros l1 l2 l3 H'; elim H'; auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4.
apply order_minusP with (l1 := l4) (l2 := pX a2 l5); auto.
apply canonical_cons; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l4); auto.
apply H'2; auto.
apply canonical_imp_canonical with (a := a1); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply H'1; auto.
apply canonical_imp_canonical with (a := a1); auto.
apply canonical_imp_canonical with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply order_minusP with (l1 := l4) (l2 := l5); auto.
apply canonical_pX_eqT with (a := a1); auto.
apply (eqT_sym A n); apply minusTerm_eqT; auto.
apply canonical_pX_eqT with (a := a2); auto.
apply (eqT_trans A n) with (y := a1); apply (eqT_sym A n); auto.
apply minusTerm_eqT; auto.
apply H'1.
apply canonical_imp_canonical with (a := a1); auto.
apply canonical_imp_canonical with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4.
apply order_minusP with (l1 := pX a1 l4) (l2 := l5); auto.
apply canonical_pX_eqT with (a := a2); auto.
apply canonical_cons; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l5); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l5); auto.
apply canonical_pX_eqT with (a := a2); auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l5); auto.
apply H'2; auto.
apply canonical_imp_canonical with (a := a2); auto.
Qed.
 
Theorem canonical_minuspf :
 forall l1 l2 : list (Term A n),
 canonical A0 eqA ltM l1 ->
 canonical A0 eqA ltM l2 -> canonical A0 eqA ltM (minuspf l1 l2).
intros l1 l2 H' H'0; generalize (minuspf_is_minusP l1 l2); intros u1.
apply canonical_minusP with (l1 := l1) (l2 := l2); auto.
Qed.
 
Lemma invTerm_eqT_comp :
 forall a b : Term A n, eqT a b -> eqT a (invTerm (A:=A) invA (n:=n) b).
intros a b H'.
apply (eqT_trans A n) with (y := b); auto.
Qed.
 
Lemma invTerm_T1_eqT_comp :
 forall a b : Term A n,
 eqT a b ->
 eqT a
   (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) b)).
intros a b H'.
apply (eqT_trans A n) with (y := b); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b);
 auto.
apply (T1_eqT A A1 eqA); auto.
Qed.
 
Lemma multTerm_invTerm_T1_eqT_comp :
 forall a b : Term A n,
 eqT a b ->
 eqT a
   (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) b).
intros a b H'.
apply (eqT_trans A n) with (y := b); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) b);
 auto.
apply (T1_eqT A A1 eqA); auto.
Qed.
Hint Resolve invTerm_eqT_comp invTerm_T1_eqT_comp
  multTerm_invTerm_T1_eqT_comp.
 
Lemma minusP_is_plusP_mults :
 forall p q r : list (Term A n),
 minusP p q r ->
 eqP A eqA n r
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p
      (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
intros p q r H'; elim H'; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
simpl in |- *; intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX a1
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec l1
               (pX
                  (multTerm (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2)))); 
 auto.
simpl in |- *; apply pluspf_inv1 with (1 := cs); auto.
change
  (ltT ltM
     (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)
     a1) in |- *.
apply eqT_compat_ltTl with (b := a2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            l1
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               l2)); auto.
simpl in |- *; apply pluspf_inv3a with (1 := cs); auto.
change
  (eqT a1
     (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2))
 in |- *.
apply (eqT_trans A n) with (y := a2); auto.
change
  (zeroP (A:=A) A0 eqA (n:=n)
     (plusTerm (A:=A) plusA (n:=n) a1
        (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
           a2))) in |- *; auto.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a1 a2);
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := plusTerm (A:=A) plusA (n:=n) a1 (invTerm (A:=A) invA (n:=n) a2));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); 
 auto.
apply eqTerm_invTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (plusTerm (A:=A) plusA (n:=n) a1
               (multTerm (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec l1
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2))); 
 auto.
apply eqpP1; auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := plusTerm (A:=A) plusA (n:=n) a1 (invTerm (A:=A) invA (n:=n) a2));
 auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
simpl in |- *; apply pluspf_inv3b with (1 := cs); auto.
change
  (eqT a1
     (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2))
 in |- *.
apply (eqT_trans A n) with (y := a2); auto.
change
  (~
   zeroP (A:=A) A0 eqA (n:=n)
     (plusTerm (A:=A) plusA (n:=n) a1
        (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
           a2))) in |- *; auto.
apply
 nzeroP_comp_eqTerm
  with (1 := cs) (a := minusTerm (A:=A) minusA (n:=n) a1 a2); 
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := plusTerm (A:=A) plusA (n:=n) a1 (invTerm (A:=A) invA (n:=n) a2));
 auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (multTerm (A:=A) multA (n:=n)
               (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pX a1 l1)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2))); 
 auto.
apply eqpP1; auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) (T1 A1 n) a2)); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
simpl in |- *; apply pluspf_inv2 with (1 := cs); auto.
change
  (ltT ltM a1
     (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a2))
 in |- *; auto.
apply eqT_compat_ltTr with (b := a2); auto.
Qed.
 
Theorem minuspf_is_pluspf_mults :
 forall p q : list (Term A n),
 eqP A eqA n (minuspf p q)
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p
      (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
intros p q; try assumption.
apply minusP_is_plusP_mults with (p := p) (q := q); auto.
Qed.
Hint Resolve minuspf_is_pluspf_mults.
 
Theorem pO_minusP_inv1 :
 forall p q : list (Term A n),
 minusP (pO A n) p q ->
 q = mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p.
intros p; elim p.
intros q H'; inversion H'; auto.
intros a l H' q H'0; inversion H'0; auto.
Qed.
 
Theorem pO_minusP_inv2 :
 forall p q : list (Term A n), minusP p (pO A n) q -> p = q.
intros p; elim p.
intros q H'; inversion H'; auto.
intros a l H' q H'0; inversion H'0; auto.
Qed.
 
Theorem minusP_inv1 :
 forall (a b : Term A n) (p q s : list (Term A n)),
 minusP (pX a p) (pX b q) s -> ltT ltM b a -> s = pX a (minuspf p (pX b q)).
intros a b p q s H'; inversion_clear H'; intros.
apply pX_inj; auto.
apply uniq_minusp with (l := (p, pX b q)); simpl in |- *; auto.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
absurd (ltT ltM b a); auto.
Qed.
 
Theorem minusP_inv2 :
 forall (a b : Term A n) (p q s : list (Term A n)),
 minusP (pX a p) (pX b q) s ->
 ltT ltM a b -> s = pX (invTerm (A:=A) invA (n:=n) b) (minuspf (pX a p) q).
intros a b p q s H'; inversion_clear H'; intros.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
apply pX_inj; auto.
apply uniq_minusp with (l := (pX a p, q)); simpl in |- *; auto.
Qed.
 
Theorem minusP_inv3a :
 forall (a b : Term A n) (p q s : list (Term A n)),
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 minusP (pX a p) (pX b q) s -> s = minuspf p q.
intros a b p q s Eqd Z0 H'; inversion_clear H'.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
apply uniq_minusp with (l := (p, q)); simpl in |- *; auto.
case H1; auto.
absurd (ltT ltM a b); auto.
Qed.
 
Theorem minusP_inv3b :
 forall (a b : Term A n) (p q s : list (Term A n)),
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 minusP (pX a p) (pX b q) s ->
 s = pX (minusTerm (A:=A) minusA (n:=n) a b) (minuspf p q).
intros a b p q s Eqd Z0 H'; inversion_clear H'.
absurd (ltT ltM b a); auto.
apply ltT_not_eqT; auto; apply eqT_sym; auto.
case Z0; auto.
apply pX_inj; auto.
apply uniq_minusp with (l := (p, q)); auto.
absurd (ltT ltM a b); auto.
Qed.
 
Theorem minuspf_inv1_eq :
 forall (a b : Term A n) (p q : list (Term A n)),
 ltT ltM b a -> pX a (minuspf p (pX b q)) = minuspf (pX a p) (pX b q).
intros a b p q H'; try assumption.
rewrite (minusP_inv1 a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv2_eq :
 forall (a b : Term A n) (p q : list (Term A n)),
 ltT ltM a b ->
 pX (invTerm (A:=A) invA (n:=n) b) (minuspf (pX a p) q) =
 minuspf (pX a p) (pX b q).
intros a b p q H'; try assumption.
rewrite (minusP_inv2 a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv3a_eq :
 forall (a b : Term A n) (p q : list (Term A n)),
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 minuspf p q = minuspf (pX a p) (pX b q).
intros a b p q H' Z; try assumption.
rewrite (minusP_inv3a a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv3b_eq :
 forall (a b : Term A n) (p q : list (Term A n)),
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 pX (minusTerm (A:=A) minusA (n:=n) a b) (minuspf p q) =
 minuspf (pX a p) (pX b q).
intros a b p q H' Z; try assumption.
rewrite (minusP_inv3b a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv1 :
 forall (a b : Term A n) (p q : list (Term A n)),
 ltT ltM b a ->
 eqP A eqA n (pX a (minuspf p (pX b q))) (minuspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
rewrite (minusP_inv1 a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv2 :
 forall (a b : Term A n) (p q : list (Term A n)),
 ltT ltM a b ->
 eqP A eqA n (pX (invTerm (A:=A) invA (n:=n) b) (minuspf (pX a p) q))
   (minuspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
rewrite (minusP_inv2 a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv3a :
 forall (a b : Term A n) (p q : list (Term A n)),
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 eqP A eqA n (minuspf p q) (minuspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
rewrite (minusP_inv3a a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem minuspf_inv3b :
 forall (a b : Term A n) (p q : list (Term A n)),
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 eqP A eqA n (pX (minusTerm (A:=A) minusA (n:=n) a b) (minuspf p q))
   (minuspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
rewrite (minusP_inv3b a b p q (minuspf (pX a p) (pX b q))); auto.
Qed.
Hint Resolve pluspf_inv1 pluspf_inv2 pluspf_inv3a pluspf_inv3b.
Hint Resolve minuspf_inv1 minuspf_inv2 minuspf_inv3a minuspf_inv3b.
 
Theorem minuspf_comp :
 forall p q r s : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 canonical A0 eqA ltM s ->
 eqP A eqA n p r ->
 eqP A eqA n q s -> eqP A eqA n (minuspf p q) (minuspf r s).
intros p q r s H' H'0 H'1 H'2 H'3 H'4;
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with
     (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
             ltM_dec p
             (mults (A:=A) multA (n:=n)
                (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
apply minuspf_is_pluspf_mults; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            r
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               s)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem mults_dist_minuspf :
 forall (p q : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 eqP A eqA n (mults (A:=A) multA (n:=n) a (minuspf p q))
   (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q)).
intros p q a H' H'0 H'1.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) a
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n) a
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n) a
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q)); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) q)); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
Hint Resolve mults_dist_minuspf.
 
Theorem minuspf_pO_refl :
 forall p : list (Term A n), eqP A eqA n (minuspf p (pO A n)) p.
intros p;
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with
     (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
             ltM_dec p
             (mults (A:=A) multA (n:=n)
                (invTerm (A:=A) invA (n:=n) (T1 A1 n)) 
                (pO A n))); auto; simpl in |- *; auto.
Qed.
Hint Resolve minuspf_pO_refl.
 
Theorem minuspf_pOmults :
 forall p : list (Term A n),
 eqP A eqA n (minuspf (pO A n) p)
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p).
intros p;
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with
     (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
             ltM_dec (pO A n)
             (mults (A:=A) multA (n:=n)
                (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p)); 
 auto; simpl in |- *; auto.
Qed.
Hint Resolve minuspf_pOmults.
 
Theorem mults_pO :
 forall (p : list (Term A n)) (a b : Term A n),
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 eqP A eqA n (pO A n)
   (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) b p)).
intros p; elim p.
simpl in |- *; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' a0 b H'0 H'1; simpl in |- *.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf (mults (A:=A) multA (n:=n) a0 l)
            (mults (A:=A) multA (n:=n) b l)); auto.
apply minuspf_inv3a; auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := multTerm (A:=A) multA (n:=n) (minusTerm (A:=A) minusA (n:=n) a0 b)
            a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multTerm_minusTerm_dist_l with (1 := cs); auto.
Qed.
 
Theorem mults_minusTerm :
 forall (p : list (Term A n)) (a b : Term A n),
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) ->
 canonical A0 eqA ltM p ->
 eqP A eqA n
   (mults (A:=A) multA (n:=n) (minusTerm (A:=A) minusA (n:=n) a b) p)
   (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) b p)).
intros p; elim p.
simpl in |- *; auto.
intros a b H H0 H1; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' a0 b H'0 H'1 H'2; simpl in |- *; auto.
cut (canonical A0 eqA ltM l); try apply canonical_imp_canonical with (a := a);
 auto; intros Z0; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (minusTerm (A:=A) minusA (n:=n)
               (multTerm (A:=A) multA (n:=n) a0 a)
               (multTerm (A:=A) multA (n:=n) b a))
            (minuspf (mults (A:=A) multA (n:=n) a0 l)
               (mults (A:=A) multA (n:=n) b l))); auto.
apply (eqpP1 A eqA); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multTerm_minusTerm_dist_l with (1 := cs); auto.
apply minuspf_inv3b; auto.
apply
 nzeroP_comp_eqTerm
  with
    (1 := cs)
    (a := multTerm (A:=A) multA (n:=n) (minusTerm (A:=A) minusA (n:=n) a0 b)
            a); auto.
apply nzeroP_multTerm with (1 := cs); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multTerm_minusTerm_dist_l with (1 := cs); auto.
Qed.
 
Theorem order_pluspf :
 forall (l1 l2 : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM (pX a l1) ->
 canonical A0 eqA ltM (pX a l2) ->
 canonical A0 eqA ltM
   (pX a
      (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l1
         l2)).
intros l1 l2 a H' H'0.
apply order_plusP with (1 := os) (plusA := plusA) (l1 := l1) (l2 := l2); auto.
apply pluspf_is_plusP; auto.
apply canonical_pluspf; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a); auto.
Qed.
Hint Resolve order_pluspf.
 
Theorem order_minuspf :
 forall (l1 l2 : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM (pX a l1) ->
 canonical A0 eqA ltM (pX a l2) ->
 canonical A0 eqA ltM (pX a (minuspf l1 l2)).
intros l1 l2 a H' H'0.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := pX a
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec l1
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l2))); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply order_pluspf; auto.
apply
 canonical_pX_eqT
  with
    (a := multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            a); auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
        (pX a l2))) in |- *; auto.
apply (eqT_sym A n); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l1); auto.
Qed.
 
Theorem minusP_refl :
 forall p q r : list (Term A n), minusP p q r -> p = q -> r = pO A n.
intros p q r H'; elim H'; auto.
intros l1 H'0; rewrite <- H'0; simpl in |- *; auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3; generalize H'0.
rewrite (pX_invl A n a1 a2 l1 l2); auto; intros Ord.
absurd (ltT ltM a2 a2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3 H'4.
apply H'1; auto.
apply pX_invr with (a := a1) (b := a2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3 H'4; elim H'3; auto.
rewrite (pX_invl A n a1 a2 l1 l2); auto.
intros a1 a2 l1 l2 l3 H'0 H'1 H'2 H'3; generalize H'0.
rewrite (pX_invl A n a1 a2 l1 l2); auto; intros Ord.
absurd (ltT ltM a2 a2); auto.
Qed.
 
Theorem minuspf_refl_eq : forall p : list (Term A n), minuspf p p = pO A n.
intros p; rewrite (minusP_refl p p (minuspf p p)); auto.
Qed.
 
Theorem minuspf_refl :
 forall p : list (Term A n), eqP A eqA n (minuspf p p) (pO A n).
intros p.
rewrite (minusP_refl p p (minuspf p p)); auto.
Qed.
 
Theorem mults_comp_minuspf :
 forall (a : Term A n) (p q : list (Term A n)),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 eqP A eqA n
   (minuspf (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q))
   (mults (A:=A) multA (n:=n) a (minuspf p q)).
intros a p q H' H'0 H'1.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) q)); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n) a
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q)); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (mults (A:=A) multA (n:=n) a
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) a
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)));
 apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem minuspf_zero :
 forall (a : Term A n) (p q : list (Term A n)),
 eqP A eqA n (minuspf (pX a p) (pX a q)) (minuspf p q).
intros a p q; try assumption.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf p q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply minuspf_inv3a; auto.
Qed.
Hint Resolve canonical_minuspf.
 
Theorem pluspf_minuspf_id :
 forall p q : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 eqP A eqA n
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (minuspf p q) q) p.
intros p q H' H'0.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)) q); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q) q)); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec q
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p (pO A n)); auto.
Qed.
 
Theorem minusP_pO_refl_eq :
 forall p q : list (Term A n), minusP p (pO A n) q -> p = q.
unfold pO in |- *; intros p q H'; inversion H'; simpl in |- *; auto.
Qed.
 
Theorem minuspf_pO_refl_eq :
 forall p : list (Term A n), minuspf p (pO A n) = p.
intros p.
rewrite <- (minusP_pO_refl_eq p (minuspf p (pO A n))); auto.
Qed.
 
Theorem Opm_ind :
 forall (P : list (Term A n) -> list (Term A n) -> Prop)
   (p q : list (Term A n)),
 (forall p : list (Term A n), P (pO A n) p) ->
 (forall p : list (Term A n), P p (pO A n)) ->
 (forall (a b : Term A n) (p q : list (Term A n)),
  P (pX a p) q -> ltT ltM a b -> P (pX a p) (pX b q)) ->
 (forall (a b : Term A n) (p q : list (Term A n)),
  P p (pX b q) -> ltT ltM b a -> P (pX a p) (pX b q)) ->
 (forall (a b : Term A n) (p q : list (Term A n)),
  P p q -> eqT a b -> P (pX a p) (pX b q)) ->
 forall p q : list (Term A n), P p q.
intros P H' H'0 H'1 H'2 H'3 H'4 H'5 p; elim p; auto.
intros a l H'6 q; elim q; auto.
intros a0 l0 H'7;
 (case (ltT_dec A n ltM ltM_dec a a0);
   [ intros temp; case temp; clear temp | idtac ]; 
   intros test); change (P (pX a l) (pX a0 l0)) in |- *; 
 auto.
Qed.
 
Theorem minuspf_eq_inv1 :
 forall (a : Term A n) (p q : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX a q) ->
 eqP A eqA n (pX a (minuspf p q)) (minuspf (pX a p) q).
intros a p q; case q; simpl in |- *; auto.
intros H' H'0; rewrite minuspf_pO_refl_eq; rewrite minuspf_pO_refl_eq; auto.
intros a0 l H' H'0.
change
  (eqP A eqA n (pX a (minuspf p (pX a0 l))) (minuspf (pX a p) (pX a0 l)))
 in |- *; apply minuspf_inv1; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
Qed.
 
Theorem minuspf_pOmults_eq :
 forall p : list (Term A n),
 minuspf (pO A n) p =
 mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p.
intros p; apply uniq_minusp with (l := (pO A n, p)); auto.
Qed.
 
Theorem minuspf_eq_inv2 :
 forall (a : Term A n) (p q : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX a q) ->
 eqP A eqA n (pX (invTerm (A:=A) invA (n:=n) a) (minuspf p q))
   (minuspf p (pX a q)).
intros a p; elim p; auto.
intros q H' H'0; rewrite minuspf_pOmults_eq.
rewrite minuspf_pOmults_eq; simpl in |- *.
apply eqpP1; auto.
change
  (eqTerm (A:=A) eqA (n:=n) (invTerm (A:=A) invA (n:=n) a)
     (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a))
 in |- *.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) (T1 A1 n) a)); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a0 l H' q H'0 H'1.
change
  (eqP A eqA n (pX (invTerm (A:=A) invA (n:=n) a) (minuspf (pX a0 l) q))
     (minuspf (pX a0 l) (pX a q))) in |- *.
rewrite <- (minuspf_inv2_eq a0 a l q); auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
Qed.
 
Definition inv : list (Term A n) -> Term A n -> Term A n.
intros p; case p.
intros a;
 exact
  (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a).
intros a1 p1 a; exact (invTerm (A:=A) invA (n:=n) a).
Defined.
 
Theorem inv_prop :
 forall (a : Term A n) (p q : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 minuspf p (pX a q) = pX (inv p a) (minuspf p q).
intros a p q; case p; simpl in |- *; auto.
intros H'.
change
  (minuspf (pO A n) (pX a q) =
   pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a)
     (minuspf (pO A n) q)) in |- *.
rewrite (minuspf_pOmults_eq (pX a q)); simpl in |- *; auto.
rewrite (minuspf_pOmults_eq q); simpl in |- *; auto.
intros a0 l H'.
change
  (minuspf (pX a0 l) (pX a q) =
   pX (invTerm (A:=A) invA (n:=n) a) (minuspf (pX a0 l) q)) 
 in |- *.
rewrite <- (minuspf_inv2_eq a0 a l q); auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
Qed.
Hint Resolve inv_prop.
 
Theorem invTerm_T1_multTerm_T1 :
 eqTerm (A:=A) eqA (n:=n)
   (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
      (invTerm (A:=A) invA (n:=n) (T1 A1 n))) (T1 A1 n).
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) (T1 A1 n)
               (invTerm (A:=A) invA (n:=n) (T1 A1 n)))); 
 [ auto | idtac ].
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)));
 auto.
apply eqTerm_invTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply T1_multTerm_l with (1 := cs);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply invTerm_invol with (1 := cs);
 auto.
Qed.
Hint Resolve invTerm_T1_multTerm_T1.
 
Theorem pluspf_is_minuspf :
 forall p q : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 eqP A eqA n
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q)
   (minuspf p
      (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q)).
intros p q Opp Opq;
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with
     (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
             ltM_dec p
             (mults (A:=A) multA (n:=n)
                (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                (mults (A:=A) multA (n:=n)
                   (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q))); 
 auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (multTerm (A:=A) multA (n:=n)
               (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (invTerm (A:=A) invA (n:=n) (T1 A1 n))) q); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with (y := mults (A:=A) multA (n:=n) (T1 A1 n) q); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Definition sminus : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (minuspf p1 p2); auto.
Defined.
End Pminus.