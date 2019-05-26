(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : addition over polynomials                       
                                                                           
          Laurent Thery March 97 (revised April 01)                          
                                                                           
  ***************************************************************************
   definition of Pplus *)
Require Export Peq.
Require Import Arith.
Section Pplus.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hEq".
 
Inductive plusP :
list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop :=
  | nillu1 : forall l1, plusP (pO A n) l1 l1
  | nillu2 : forall l1, plusP l1 (pO A n) l1
  | mainu1 :
      forall a1 a2 l1 l2 l3,
      ltT ltM a2 a1 ->
      plusP l1 (pX a2 l2) l3 -> plusP (pX a1 l1) (pX a2 l2) (pX a1 l3)
  | mainu2a :
      forall a1 a2 l1 l2 l3,
      plusP l1 l2 l3 ->
      eqT a1 a2 ->
      zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a2) ->
      plusP (pX a1 l1) (pX a2 l2) l3
  | mainu2b :
      forall a1 a2 l1 l2 l3,
      plusP l1 l2 l3 ->
      eqT a1 a2 ->
      ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a2) ->
      plusP (pX a1 l1) (pX a2 l2)
        (pX (plusTerm (A:=A) plusA (n:=n) a1 a2) l3)
  | mainu3 :
      forall a1 a2 l1 l2 l3,
      ltT ltM a1 a2 ->
      plusP (pX a1 l1) l2 l3 -> plusP (pX a1 l1) (pX a2 l2) (pX a2 l3).
Hint Resolve nillu1 nillu2 mainu1 mainu2a mainu2b mainu3.
 
Definition projsig1 (A : Set) (P : A -> Prop) (H : sig P) :=
  let (a, _) return A := H in a.
Require Import LetP.
 
Definition plusp : forall l, {a : _ | plusP (fst l) (snd l) a}.
intros l; pattern l in |- *.
apply well_founded_induction with (R := lessP A n); auto.
apply wf_lessP; auto.
intros x; case x; intros p q; simpl in |- *.
case p; clear p.
intros H'; exists q; auto.
intros a1 m1; case q; clear q.
intros H'; exists (pX a1 m1); auto.
intros a2 m2 H'; case (ltT_dec A n ltM ltM_dec a1 a2);
 [ intros P; case P; clear P | idtac ]; intros H1.
lapply (H' (pX a1 m1, m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX a2 Orec); auto.
change (plusP (pX a1 m1) (pX a2 m2) (pX a2 Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
lapply (H' (m1, pX a2 m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX a1 Orec); auto.
change (plusP (pX a1 m1) (pX a2 m2) (pX a1 Orec)) in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
apply LetP with (h := plusTerm (A:=A) plusA (n:=n) a1 a2).
intros letA eqL0; case (zeroP_dec A A0 eqA eqA_dec n letA); intros H'0.
lapply (H' (m1, m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists Orec; auto.
change (plusP (pX a1 m1) (pX a2 m2) Orec) in |- *; auto.
rewrite eqL0 in H'0; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
lapply (H' (m1, m2)); simpl in |- *;
 [ intros Rec; case Rec; clear Rec; intros Orec Prec | idtac ].
exists (pX letA Orec); auto.
change (plusP (pX a1 m1) (pX a2 m2) (pX letA Orec)) in |- *; auto.
rewrite eqL0; auto.
rewrite eqL0 in H'0; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
Defined.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition pluspf l1 l2 := projsig1 _ _ (plusp (l1, l2)).
Hint Unfold projsig1 pluspf.
Set Strict Implicit.
Unset Implicit Arguments.
 
Lemma plusP_inv :
 forall p q l (a b : Term A n),
 plusP (pX a p) (pX b q) l ->
 exists l1 : _,
   ltT ltM b a /\ plusP p (pX b q) l1 /\ l = pX a l1 \/
   ltT ltM a b /\ plusP (pX a p) q l1 /\ l = pX b l1 \/
   eqT a b /\
   (zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) /\
    plusP p q l \/
    ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) /\
    plusP p q l1 /\ l = pX (plusTerm (A:=A) plusA (n:=n) a b) l1).
intros p q l a b H'; simple inversion H'.
discriminate H.
discriminate H0.
rewrite <- H3; rewrite (pX_invl _ _ a2 b l2 q H2);
 rewrite (pX_invr _ _ l2 q a2 b H2); rewrite (pX_invl _ _ a1 a l1 p H1);
 rewrite (pX_invr _ _ l1 p a1 a H1).
intros H'0 H'1; exists l3; left; split;
 [ idtac | split; [ try assumption | idtac ] ]; auto.
rewrite <- H3.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- (pX_invl _ _ a2 b l2 q H3); rewrite <- (pX_invl _ _ a1 a l1 p H2);
 auto.
rewrite <- (pX_invr _ _ l2 q a2 b H3); rewrite <- (pX_invr _ _ l1 p a1 a H2);
 auto.
rewrite <- H4; auto.
intros H'0 H'1 H'2; exists l3; right; right.
rewrite <- (pX_invl _ _ a2 b l2 q H3); rewrite <- (pX_invl _ _ a1 a l1 p H2);
 auto.
rewrite <- (pX_invr _ _ l2 q a2 b H3); rewrite <- (pX_invr _ _ l1 p a1 a H2);
 auto.
intros H'0 H'1; exists l3; right; left; split;
 [ idtac | split; [ try assumption | idtac ] ]; auto.
rewrite <- (pX_invl _ _ a2 b l2 q H2); rewrite <- (pX_invl _ _ a1 a l1 p H1);
 auto.
rewrite <- (pX_invl _ _ a1 a l1 p H1); rewrite <- (pX_invr _ _ l2 q a2 b H2);
 rewrite <- (pX_invr _ _ l1 p a1 a H1); auto.
rewrite <- H3; rewrite <- (pX_invl _ _ a2 b l2 q H2); auto.
Qed.
 
Theorem uniq_plusp :
 forall l l3 l4,
 plusP (fst l) (snd l) l3 -> plusP (fst l) (snd l) l4 -> l3 = l4.
intros l; pattern l in |- *.
apply well_founded_ind with (1 := wf_lessP A n).
intros (l1, l2); simpl in |- *.
case l1; clear l1.
intros H' l3 l4 H'0; inversion_clear H'0; intros H'2; inversion_clear H'2;
 auto.
case l2; clear l2.
simpl in |- *; intros n0 l0 H' l3 l4 H'0 H'2; inversion H'2; inversion H'0;
 auto.
simpl in |- *; intros n2 l2 n1 l1 Induc l3 l4 Hl3 Hl4.
case (plusP_inv l1 l2 l4 n1 n2); auto.
intros x H'; elim H';
 [ intros H'0; elim H'0; intros H'1 H'2; elim H'2; intros H'3 H'4;
    rewrite H'4; clear H'2 H'0 H'
 | intros H'0; clear H' ].
case (plusP_inv l1 l2 l3 n1 n2); auto.
intros x0 H'; elim H';
 [ intros H'0; elim H'0; intros H'2 H'5; elim H'5; intros H'6 H'7;
    rewrite H'7; clear H'5 H'0 H'
 | intros H'0; clear H' ]; auto.
apply pX_inj; auto.
apply Induc with (y := (l1, n2 :: l2)); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
elim H'0;
 [ intros H'; elim H'; intros H'2 H'5; clear H' H'0 | intros H'; clear H'0 ].
absurd (ltT ltM n1 n2); auto.
elim H'; intros H'0 H'2; try exact H'0; clear H'.
absurd (eqT n2 n1); auto.
apply (eqT_sym A n n1); auto.
elim H'0;
 [ intros H'; elim H'; intros H'1 H'2; elim H'2; intros H'3 H'4; rewrite H'4;
    clear H'2 H' H'0
 | intros H'; clear H'0 ].
case (plusP_inv l1 l2 l3 n1 n2); auto.
intros x0 H'; elim H';
 [ intros H'0; elim H'0; intros H'2 H'5; clear H'0 H'
 | intros H'0; clear H' ].
absurd (ltT ltM n1 n2); auto.
elim H'0;
 [ intros H'; elim H'; intros H'2 H'5; elim H'5; intros H'6 H'7; rewrite H'7;
    clear H'5 H' H'0
 | intros H'; clear H'0 ].
apply pX_inj; auto.
apply Induc with (y := (pX n1 l1, l2)); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
elim H'; intros H'0 H'2; try exact H'0; clear H'.
absurd (eqT n1 n2); auto.
elim H'; intros H'0 H'1; try exact H'0; clear H'.
case (plusP_inv l1 l2 l3 n1 n2); auto.
intros x0 H'; elim H';
 [ intros H'2; elim H'2; intros H'3 H'4; try exact H'3; clear H'2 H'
 | intros H'2; clear H' ].
absurd (eqT n2 n1); auto.
apply (eqT_sym A n n1); auto.
elim H'2;
 [ intros H'; elim H'; intros H'3 H'4; try exact H'3; clear H' H'2
 | intros H'; clear H'2 ].
absurd (eqT n1 n2); auto.
elim H'; intros H'2 H'3; elim H'3;
 [ intros H'4; elim H'4; intros H'5 H'6; try exact H'5; clear H'4 H'3 H'
 | intros H'4; clear H'3 H' ].
elim H'1;
 [ intros H'; clear H'1
 | intros H'; elim H'; intros H'3 H'4; apply H'3 || elim H'3; clear H' H'1 ];
 auto.
elim H'; intros H'1 H'3; clear H'.
apply Induc with (y := (l1, l2)); auto; red in |- *; simpl in |- *; auto.
simpl in |- *; auto with arith.
elim H'4; intros H' H'3; elim H'3; intros H'5 H'6; rewrite H'6; clear H'3 H'4.
elim H'1;
 [ intros H'3; clear H'1
 | intros H'3; elim H'3; intros H'4 H'7; elim H'7; intros H'8 H'9;
    rewrite H'9; clear H'7 H'3 H'1 ].
elim H'3; intros H'1 H'4; try exact H'1; clear H'3.
apply H' || elim H'; try assumption.
apply pX_inj; auto.
apply Induc with (y := (l1, l2)); auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
Qed.
 
Theorem pluspf_is_plusP : forall l1 l2, plusP l1 l2 (pluspf l1 l2).
intros l1 l2; try assumption.
unfold pluspf in |- *; case (plusp (l1, l2)); simpl in |- *; auto.
Qed.
Hint Resolve pluspf_is_plusP.
 
Theorem order_plusP :
 forall l1 l2 l3 a,
 plusP l1 l2 l3 ->
 canonical A0 eqA ltM (pX a l1) ->
 canonical A0 eqA ltM (pX a l2) ->
 canonical A0 eqA ltM l3 -> canonical A0 eqA ltM (pX a l3).
intros l1 l2 l3 a H'; generalize a; elim H'; auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 a0 H'3 H'4 H'5.
apply canonical_cons; auto.
apply (canonical_pX_order _ A0 eqA) with (l := l4); auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := pX a1 l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 a0 H'4 H'5 H'6.
apply H'1; auto.
apply canonical_skip_fst with (b := a1); auto.
apply canonical_skip_fst with (b := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 a0 H'4 H'5 H'6.
apply canonical_cons; auto.
apply ltT_eqTr with (a := a1); auto.
apply (eqT_sym A n (plusTerm (A:=A) plusA (n:=n) a1 a2)).
apply plusTerm_eqT1; auto.
apply (canonical_pX_order _ A0 eqA) with (l := l4); auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := pX a1 l4); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 a0 H'3 H'4 H'5.
apply canonical_cons; auto.
apply (canonical_pX_order _ A0 eqA) with (l := l5); auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := pX a1 l4); auto.
Qed.
 
Theorem canonical_plusP :
 forall l1 l2 l3,
 plusP l1 l2 l3 ->
 canonical A0 eqA ltM l1 ->
 canonical A0 eqA ltM l2 -> canonical A0 eqA ltM l3.
intros l1 l2 l3 H'; elim H'; auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4; try assumption.
apply order_plusP with (l1 := l4) (l2 := pX a2 l5); auto.
apply canonical_cons; auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l4); auto.
apply H'2; auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a1); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply H'1; auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a1); auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4 H'5.
apply order_plusP with (l1 := l4) (l2 := l5); auto.
apply canonical_pX_eqT with (a := a1); auto.
apply (eqT_sym A n (plusTerm (A:=A) plusA (n:=n) a1 a2)).
apply plusTerm_eqT1; auto.
apply canonical_pX_eqT with (a := a2); auto; auto.
apply (eqT_sym A n (plusTerm (A:=A) plusA (n:=n) a1 a2)).
apply plusTerm_eqT2; auto.
apply H'1.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a1); auto.
apply (canonical_imp_canonical _ A0 eqA _ ltM) with (a := a2); auto.
intros a1 a2 l4 l5 l6 H'0 H'1 H'2 H'3 H'4.
apply order_plusP with (l1 := pX a1 l4) (l2 := l5); auto.
apply canonical_cons; auto.
apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l5); auto.
apply H'2; auto.
apply canonical_imp_canonical with (a := a2); auto.
Qed.
 
Theorem canonical_pluspf :
 forall l1 l2,
 canonical A0 eqA ltM l1 ->
 canonical A0 eqA ltM l2 -> canonical A0 eqA ltM (pluspf l1 l2).
intros l1 l2 H' H'0; generalize (pluspf_is_plusP l1 l2); intros u1.
apply canonical_plusP with (l1 := l1) (l2 := l2); auto.
Qed.
 
Theorem pO_plusP_inv1 : forall p q, plusP (pO A n) p q -> p = q.
intros p; elim p.
intros q H'; inversion H'; auto.
intros a l H' q H'0; inversion H'0; auto.
Qed.
Hint Resolve eqp_refl.
 
Theorem pO_plusP_inv2 : forall p q, plusP p (pO A n) q -> p = q.
intros p; elim p.
intros q H'; inversion H'; auto.
intros a l H' q H'0; inversion H'0; auto.
Qed.
Hint Resolve eqp_refl.
 
Theorem plusP_decomp :
 forall a p,
 canonical A0 eqA ltM (pX a p) -> plusP (pX a (pO A n)) p (pX a p).
intros a p; case p; auto.
intros m l H'; try assumption.
change (plusP (pX a (pO A n)) (pX m l) (pX a (pX m l))) in |- *.
apply mainu1; auto.
apply (canonical_pX_order _ A0 eqA) with (l := l); auto.
Qed.
 
Theorem plusP_inv1 :
 forall a b p q s,
 plusP (pX a p) (pX b q) s -> ltT ltM b a -> s = pX a (pluspf p (pX b q)).
unfold pX in |- *; intros a b p q s H'; inversion_clear H'; intros.
change (pX a l3 = pX a (pluspf p (pX b q))) in |- *; apply pX_inj; auto.
apply uniq_plusp with (l := (p, pX b q)); simpl in |- *; auto.
absurd (eqT b a); auto.
apply eqT_sym; auto.
absurd (eqT b a); auto.
apply eqT_sym; auto.
absurd (ltT ltM b a); auto.
Qed.
 
Theorem plusP_inv2 :
 forall a b p q s,
 plusP (pX a p) (pX b q) s -> ltT ltM a b -> s = pX b (pluspf (pX a p) q).
intros a b p q s H'; inversion_clear H'; intros.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
absurd (ltT ltM a b); auto.
apply pX_inj; auto.
apply uniq_plusp with (l := (pX a p, q)); simpl in |- *; auto.
Qed.
 
Theorem plusP_inv3a :
 forall a b p q s,
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 plusP (pX a p) (pX b q) s -> s = pluspf p q.
intros a b p q s Eqd Z0 H'; inversion_clear H'; intros.
absurd (eqT b a); auto.
apply eqT_sym; auto.
apply uniq_plusp with (l := (p, q)); auto.
elim H1; auto.
absurd (eqT a b); auto.
Qed.
 
Theorem plusP_inv3b :
 forall a b p q s,
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 plusP (pX a p) (pX b q) s ->
 s = pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q).
unfold pX in |- *; intros a b p q s Eqd Z0 H'; inversion_clear H'; intros.
absurd (eqT b a); auto.
apply eqT_sym; auto.
elim Z0; try assumption.
change
  (pX (plusTerm (A:=A) plusA (n:=n) a b) l3 =
   pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q)) 
 in |- *.
apply pX_inj; auto.
apply uniq_plusp with (l := (p, q)); auto.
absurd (eqT a b); auto.
Qed.
 
Theorem pluspf_inv1 :
 forall a b p q,
 ltT ltM b a ->
 eqP A eqA n (pX a (pluspf p (pX b q))) (pluspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
rewrite (plusP_inv1 a b p q (pluspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem pluspf_inv2 :
 forall a b p q,
 ltT ltM a b ->
 eqP A eqA n (pX b (pluspf (pX a p) q)) (pluspf (pX a p) (pX b q)).
intros a b p q H'; try assumption.
rewrite (plusP_inv2 a b p q (pluspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem pluspf_inv3a :
 forall a b p q,
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 eqP A eqA n (pluspf p q) (pluspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
rewrite (plusP_inv3a a b p q (pluspf (pX a p) (pX b q))); auto.
Qed.
 
Theorem pluspf_inv3b :
 forall a b p q,
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 eqP A eqA n (pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q))
   (pluspf (pX a p) (pX b q)).
intros a b p q H' Z; try assumption.
rewrite (plusP_inv3b a b p q (pluspf (pX a p) (pX b q))); auto.
Qed.
Hint Resolve pluspf_inv1 pluspf_inv2 pluspf_inv3a pluspf_inv3b.
 
Theorem plusP_com :
 forall p q r s, plusP p q r -> plusP q p s -> eqP A eqA n r s.
intros p q r s H'; generalize s; elim H'; clear s H'; auto.
intros l1 s H'; try assumption.
rewrite (pO_plusP_inv2 l1 s); auto.
intros l1 s H'; rewrite (pO_plusP_inv1 l1 s); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 s H'2.
rewrite (plusP_inv2 a2 a1 l2 l1 s); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 H'2 s R.
rewrite (plusP_inv3a a2 a1 l2 l1 s); auto.
apply (eqT_sym A n a1); auto.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a1 a2);
 auto.
apply plusTerm_com with (1 := cs); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 H'2 s H'3.
rewrite (plusP_inv3b a2 a1 l2 l1 s); auto.
apply eqpP1; auto; apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n a1); auto.
red in |- *; intros H'4; apply H'2.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a2 a1);
 auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n); auto.
intros a1 a2 l1 l2 l3 H' H'0 H'1 s H'2.
rewrite (plusP_inv1 a2 a1 l2 l1 s); auto.
Qed.
 
Theorem pluspf_com : forall p q, eqP A eqA n (pluspf p q) (pluspf q p).
intros p q; apply (plusP_com p q (pluspf p q) (pluspf q p)); auto.
Qed.
 
Theorem plusP_zero_pOl : forall p q, plusP (pO A n) p q -> eqP A eqA n p q.
intros p q H'; inversion H'; auto.
Qed.
 
Theorem plusP_zero_pOr : forall p q, plusP p (pO A n) q -> eqP A eqA n p q.
intros p q H'; inversion H'; auto.
Qed.
Hint Resolve plusP_zero_pOl plusP_zero_pOr.
Hint Resolve eqp_trans.
 
Theorem plusP_uniq_eqP :
 forall p q r s, plusP p q r -> plusP p q s -> eqP A eqA n r s.
intros p q r s H' H'0; rewrite (uniq_plusp (p, q) r s); auto.
Qed.
Hint Resolve plusP_uniq_eqP.
 
Theorem pO_pluspf_inv1 : forall p, p = pluspf (pO A n) p.
intros p.
apply uniq_plusp with (l := (pO A n, p)); auto.
Qed.
 
Theorem pO_pluspf_inv2 : forall p, p = pluspf p (pO A n).
intros p.
apply uniq_plusp with (l := (p, pO A n)); auto.
Qed.
 
Theorem pluspf_inv1_eq :
 forall a b p q,
 ltT ltM b a -> pX a (pluspf p (pX b q)) = pluspf (pX a p) (pX b q).
intros a b p q H'; rewrite (plusP_inv1 a b p q (pluspf (pX a p) (pX b q)));
 auto.
Qed.
 
Theorem pluspf_inv2_eq :
 forall a b p q,
 ltT ltM a b -> pX b (pluspf (pX a p) q) = pluspf (pX a p) (pX b q).
intros a b p q H'; rewrite (plusP_inv2 a b p q (pluspf (pX a p) (pX b q)));
 auto.
Qed.
 
Theorem pluspf_inv3a_eq :
 forall a b p q,
 eqT a b ->
 zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 pluspf p q = pluspf (pX a p) (pX b q).
intros a b p q H' H1';
 rewrite (plusP_inv3a a b p q (pluspf (pX a p) (pX b q))); 
 auto.
Qed.
 
Theorem pluspf_inv3b_eq :
 forall a b p q,
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 pX (plusTerm (A:=A) plusA (n:=n) a b) (pluspf p q) =
 pluspf (pX a p) (pX b q).
intros a b p q H' H1';
 rewrite (plusP_inv3b a b p q (pluspf (pX a p) (pX b q))); 
 auto.
Qed.
 
Theorem order_pluspf :
 forall l1 l2 a,
 canonical A0 eqA ltM (pX a l1) ->
 canonical A0 eqA ltM (pX a l2) -> canonical A0 eqA ltM (pX a (pluspf l1 l2)).
intros l1 l2 a H' H'0.
apply order_plusP with (l1 := l1) (l2 := l2); auto.
apply canonical_pluspf; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a); auto.
Qed.
 
Theorem pluspf_inv1_eqa :
 forall a p q,
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX a q) -> pX a (pluspf p q) = pluspf (pX a p) q.
intros a p q; case q; auto.
rewrite <- pO_pluspf_inv2; auto.
rewrite <- pO_pluspf_inv2; auto.
intros a0 l H'0 H'1.
change (pX a (pluspf p (pX a0 l)) = pluspf (pX a p) (pX a0 l)) in |- *.
apply pluspf_inv1_eq; auto.
apply (canonical_pX_order _ A0 eqA) with (l := l); auto.
Qed.
 
Theorem pluspf_inv2_eqa :
 forall a p q,
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX a q) -> pX a (pluspf p q) = pluspf p (pX a q).
intros a p; case p; auto.
intros q H'0 H'1.
rewrite <- pO_pluspf_inv1; auto.
rewrite <- pO_pluspf_inv1; auto.
intros a0 l q H'0 H'1.
change (pX a (pluspf (pX a0 l) q) = pluspf (pX a0 l) (pX a q)) in |- *.
apply pluspf_inv2_eq; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
Qed.
 
Theorem p0_pluspf_l : forall p, eqP A eqA n (pluspf (pO A n) p) p.
intros p; rewrite <- pO_pluspf_inv1; auto.
Qed.
 
Theorem p0_pluspf_r : forall p, eqP A eqA n (pluspf p (pO A n)) p.
intros p; rewrite <- pO_pluspf_inv2; auto.
Qed.
Hint Resolve p0_pluspf_l p0_pluspf_r.
 
Theorem plusTerm_is_pX :
 forall (a : Term A n) (p : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 eqP A eqA n (pluspf (pX a (pO A n)) p) (pX a p).
intros a p; case p; auto.
intros a0 l H'.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := pX a (pluspf (pO A n) (a0 :: l))); auto.
change
  (eqP A eqA n (pluspf (pX a (pO A n)) (pX a0 l))
     (pX a (pluspf (pO A n) (pX a0 l)))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply pluspf_inv1; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
Qed.
Hint Resolve plusTerm_is_pX.
 
Theorem pluspf3_assoc :
 forall l,
 canonical A0 eqA ltM (fst l) ->
 canonical A0 eqA ltM (fst (snd l)) ->
 canonical A0 eqA ltM (snd (snd l)) ->
 eqP A eqA n (pluspf (pluspf (fst l) (fst (snd l))) (snd (snd l)))
   (pluspf (fst l) (pluspf (fst (snd l)) (snd (snd l)))).
intros l; pattern l in |- *.
apply (well_founded_ind (wf_lessP3 A n)).
intros x; case x; intros p z; case z; intros q r; simpl in |- *; clear x z;
 auto.
case p.
rewrite <- pO_pluspf_inv1; auto.
case q.
intros a l0; rewrite <- pO_pluspf_inv1; rewrite <- pO_pluspf_inv2; auto.
case r; simpl in |- *; auto.
intros a l0 a0 l1; rewrite <- pO_pluspf_inv2; rewrite <- pO_pluspf_inv2; auto.
intros a l0 a0 l1 a1 l2 H' H'0 H'1 H'2.
cut (canonical A0 eqA ltM (pX a l0)); [ clear H'2; intros H'2 | auto ].
cut (canonical A0 eqA ltM (pX a0 l1)); [ clear H'1; intros H'1 | auto ].
cut (canonical A0 eqA ltM (pX a1 l2)); [ clear H'0; intros H'0 | auto ].
cut (canonical A0 eqA ltM l0);
 [ intros C0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM l1);
 [ intros C1 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
cut (canonical A0 eqA ltM l2);
 [ intros C2 | apply canonical_imp_canonical with (a := a1) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZ0 | apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l0) ];
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros nZ1 | apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l1) ];
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1);
 [ intros nZ2 | apply (canonical_nzeroP _ A0 eqA _ ltM) with (p := l2) ];
 auto.
change
  (eqP A eqA n (pluspf (pluspf (pX a1 l2) (pX a0 l1)) (pX a l0))
     (pluspf (pX a1 l2) (pluspf (pX a0 l1) (pX a l0)))) 
 in |- *.
case (ltT_dec A n ltM ltM_dec a1 a0);
 [ intros H0; case H0; clear H0 | idtac ]; intros H0.
case (ltT_dec A n ltM ltM_dec a0 a); [ intros H1; case H1; clear H1 | idtac ];
 intros H1.
cut (ltT ltM a1 a);
 [ intros Ord0 | apply (ltT_trans A _ _ os) with (y := a0) ]; 
 auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv2_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply eqpP1; auto.
rewrite (pluspf_inv2_eq a1 a0 l2 l1); auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
rewrite <- (pluspf_inv1_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
apply eqpP1; auto.
apply H' with (y := (pX a1 l2, (l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
cut (ltT ltM a1 a); [ intros Ord0 | apply eqT_compat_ltTr with (b := a0) ];
 auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a));
 intros Z0.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv3a_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
apply H' with (y := (pX a1 l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l2)); auto.
repeat rewrite (plus_comm (size A n l1)); auto.
cut (ltT ltM a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 [ intros Ord1
 | apply eqT_compat_ltTr with (b := a0); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv2_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3b_eq a0 a (pluspf (pX a1 l2) l1) l0); auto.
rewrite <-
 (pluspf_inv2_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0))
 ; auto.
apply eqpP1; auto.
apply H' with (y := (pX a1 l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l2)); auto.
repeat rewrite (plus_comm (size A n l1)); auto.
rewrite <- (pluspf_inv1_eq a1 a0 l2 l1); auto.
case (ltT_dec A n ltM ltM_dec a0 a); [ intros H1; case H1; clear H1 | idtac ];
 intros H1.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
case (ltT_dec A n ltM ltM_dec a1 a); [ intros H2; case H2; clear H2 | idtac ];
 intros H2.
rewrite <- (pluspf_inv2_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply eqpP1; auto.
rewrite (pluspf_inv1_eq a1 a0 l2 l1); auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
rewrite <- (pluspf_inv1_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
apply eqpP1; auto.
rewrite (pluspf_inv2_eq a0 a l1 l0); auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
cut (ltT ltM a0 (plusTerm (A:=A) plusA (n:=n) a1 a));
 [ intros Ord1
 | apply eqT_compat_ltTr with (b := a1); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT1 A plusA n) ]; auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a1 a));
 intros Z0.
rewrite <- (pluspf_inv3a_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv3a_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply H' with (y := (l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
rewrite <- (pluspf_inv3b_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <- (pluspf_inv3b_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply eqpP1; auto.
apply H' with (y := (l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
cut (ltT ltM a a1);
 [ intros Ord0 | apply (ltT_trans A n ltM os) with (y := a0) ];
 auto with arith.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
apply eqpP1; auto.
rewrite (pluspf_inv1_eq a0 a l1 l0); auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
cut (ltT ltM a a1);
 [ intros Ord0 | apply eqT_compat_ltTl with (b := a0); auto ]; 
 auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a));
 intros Z0.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eqa a1 l2 (pluspf l1 l0)); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
apply eqpP1; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := pluspf l2 (pluspf (pX a0 l1) (pX a l0))); 
 auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
apply order_pluspf; auto.
apply canonical_skip_fst with (b := a0); auto.
apply canonical_skip_fst with (b := a); auto.
cut (ltT ltM (plusTerm (A:=A) plusA (n:=n) a0 a) a1);
 [ intros Ord1
 | apply eqT_compat_ltTl with (b := a0); auto; apply (eqT_sym A n); auto;
    apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eq a1 a (pluspf l2 (pX a0 l1)) l0); auto.
rewrite <-
 (pluspf_inv1_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0))
 ; auto.
apply eqpP1; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := pluspf l2 (pluspf (pX a0 l1) (pX a l0))); 
 auto.
apply H' with (y := (l2, (pX a0 l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a1 a0));
 intros Z0.
rewrite <- (pluspf_inv3a_eq a1 a0 l2 l1); auto.
case (ltT_dec A n ltM ltM_dec a1 a); [ intros H2; case H2; clear H2 | idtac ];
 intros H2.
cut (ltT ltM a0 a); [ intros Ord0 | apply eqT_compat_ltTl with (b := a1) ];
 auto.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := pX a (pluspf (pluspf (pX a1 l2) (pX a0 l1)) l0)); 
 auto.
rewrite <- (pluspf_inv3a_eq a1 a0 l2 l1); auto.
rewrite <- (pluspf_inv2_eqa a (pluspf l2 l1) l0); auto.
apply order_pluspf; auto.
apply canonical_skip_fst with (b := a1); auto.
apply canonical_skip_fst with (b := a0); auto.
apply eqpP1; auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
cut (ltT ltM a a0); [ intros Ord0 | apply eqT_compat_ltTr with (b := a1) ];
 auto.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3a_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
apply H' with (y := (l2, (l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a));
 intros Z1.
cut (eqT a0 a);
 [ intros eqTerm0
 | apply (eqT_trans A n) with (y := a1); auto; apply (eqT_sym A n) ]; 
 auto.
cut (eqT a (plusTerm (A:=A) plusA (n:=n) a1 a0));
 [ intros eqTerm1
 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); auto;
    apply (plusTerm_eqT2 A plusA n) ]; auto.
cut (eqT (plusTerm (A:=A) plusA (n:=n) a a1) a0);
 [ intros eqTerm2
 | apply (eqT_trans A n) with (y := a);
    [ apply (plusTerm_eqT1 A plusA n)
    | apply (eqT_trans A n) with (y := a1) ]; auto; 
    apply (eqT_sym A n) ]; auto.
cut (eqT (plusTerm (A:=A) plusA (n:=n) a1 a) a0);
 [ intros eqTerm3
 | apply (eqT_trans A n) with (y := a); auto;
    [ apply (plusTerm_eqT2 A plusA n) | apply (eqT_sym A n) ] ]; 
 auto.
cut (eqT a1 (plusTerm (A:=A) plusA (n:=n) a a0));
 [ intros eqTerm4
 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT2 A plusA n); auto; apply (eqT_sym A n) ]; 
 auto.
cut (eqT a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 [ intros eqTerm5
 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eqa a (pluspf l2 l1) l0); auto.
rewrite <- (pluspf_inv1_eqa a1 l2 (pluspf l1 l0)); auto.
apply eqpP1; auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a (plusTerm (A:=A) plusA (n:=n) a1 a0));
 auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a a0));
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a a1) a0);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqT_sym A n); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a) a0);
 auto.
apply plusTerm_comp_l with (1 := cs); auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply plusTerm_com with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply zeroP_plusTermr with (1 := cs); auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a0); auto.
apply (eqT_sym A n); auto.
apply canonical_pX_eqT with (a := a); auto.
apply (eqT_sym A n); auto.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a1); auto.
apply canonical_pX_eqT with (a := a0); auto.
cut (eqT a0 a);
 [ intros Ord0
 | apply (eqT_trans A n) with (y := a1); auto; apply (eqT_sym A n) ]; 
 auto.
cut (eqT a (plusTerm (A:=A) plusA (n:=n) a1 a0));
 [ intros eqTerm1
 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n); auto;
    apply (plusTerm_eqT2 A plusA n) ]; auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
rewrite <-
 (pluspf_inv3b_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0))
 ; auto.
rewrite <- (pluspf_inv2_eqa a (pluspf l2 l1) l0); auto.
apply eqpP1; auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a (plusTerm (A:=A) plusA (n:=n) a1 a0));
 auto.
apply zeroP_plusTermr with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a);
 auto.
apply plusTerm_com with (1 := cs); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a1); auto.
apply canonical_pX_eqT with (a := a0); auto.
apply (eqT_trans A n) with (y := a); auto; apply (eqT_sym A n); auto.
apply (plusTerm_eqT2 A plusA n); auto.
red in |- *; intros H'3; absurd (zeroP (A:=A) A0 eqA (n:=n) a); auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply zeroP_plusTerml with (1 := cs); auto.
apply (eqT_sym A n); auto.
rewrite <- (pluspf_inv3b_eq a1 a0 l2 l1); auto.
case (ltT_dec A n ltM ltM_dec a0 a); [ intros H1; case H1; clear H1 | idtac ];
 intros H1.
cut (ltT ltM a1 a);
 [ intros Ord0
 | apply eqT_compat_ltTl with (b := a0); auto; apply (eqT_sym A n) ]; 
 auto.
cut (ltT ltM (plusTerm (A:=A) plusA (n:=n) a1 a0) a);
 [ intros Ord1
 | apply eqT_compat_ltTl with (b := a1); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT1 A plusA n) ]; auto.
rewrite <- (pluspf_inv2_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv2_eq a1 a l2 (pluspf (pX a0 l1) l0)); auto.
rewrite <-
 (pluspf_inv2_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0)
 ; auto.
apply eqpP1; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := pluspf (pluspf (pX a1 l2) (pX a0 l1)) l0); 
 auto.
rewrite <- (pluspf_inv3b_eq a1 a0 l2 l1); auto.
apply H' with (y := (pX a1 l2, (pX a0 l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
repeat rewrite (fun a b : nat => plus_comm a (S b)); simpl in |- *.
repeat rewrite (plus_comm (size A n l1)); auto.
cut (ltT ltM a a1);
 [ intros Ord0
 | apply eqT_compat_ltTr with (b := a0); auto; apply (eqT_sym A n) ]; 
 auto.
cut (ltT ltM a (plusTerm (A:=A) plusA (n:=n) a1 a0));
 [ intros Ord1
 | apply eqT_compat_ltTr with (b := a0); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT2 A plusA n) ]; auto.
rewrite <- (pluspf_inv1_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv3b_eq a1 a0 l2 (pluspf l1 (pX a l0))); auto.
rewrite <-
 (pluspf_inv1_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0)
 ; auto.
apply eqpP1; auto.
apply H' with (y := (l2, (l1, pX a l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
cut (eqT a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 [ intros eqTerm1
 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n);
    apply (plusTerm_eqT1 A plusA n) ]; auto.
cut (eqT a1 a);
 [ intros eqT0
 | apply (eqT_trans A n) with (y := a0); auto; apply (eqT_sym A n) ]; 
 auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a0 a));
 intros Z1.
rewrite <- (pluspf_inv3a_eq a0 a l1 l0); auto.
rewrite <- (pluspf_inv1_eqa a1 l2 (pluspf l1 l0)); auto.
cut
 (~
  zeroP (A:=A) A0 eqA (n:=n)
    (plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a));
 [ intros Z2 | idtac ].
rewrite <-
 (pluspf_inv3b_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0)
 ; auto.
apply eqpP1; auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply zeroP_plusTermr with (1 := cs); auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply (eqT_trans A n) with (y := a1); auto.
apply (plusTerm_eqT1 A plusA n); auto.
red in |- *; intros H'3; absurd (zeroP (A:=A) A0 eqA (n:=n) a1); auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a);
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a));
 auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply zeroP_plusTermr with (1 := cs); auto.
apply order_pluspf; auto.
apply canonical_pX_eqT with (a := a0); auto.
apply (eqT_trans A n) with a; auto.
apply (eqT_sym A n); auto.
apply canonical_pX_eqT with (a := a); auto.
apply (eqT_sym A n); auto.
rewrite <- (pluspf_inv3b_eq a0 a l1 l0); auto.
cut
 (eqTerm eqA
    (plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a)
    (plusTerm (A:=A) plusA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a0 a)));
 [ intros eqTerm0 | idtac ].
case
 (zeroP_dec A A0 eqA eqA_dec n
    (plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a));
 intros Z2.
rewrite <-
 (pluspf_inv3a_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0)
 ; auto.
rewrite <-
 (pluspf_inv3a_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0))
 ; auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a);
 auto.
apply (eqT_trans A n) with (y := a0); auto.
apply (plusTerm_eqT2 A plusA n); auto.
rewrite <-
 (pluspf_inv3b_eq (plusTerm (A:=A) plusA (n:=n) a1 a0) a (pluspf l2 l1) l0)
 ; auto.
rewrite <-
 (pluspf_inv3b_eq a1 (plusTerm (A:=A) plusA (n:=n) a0 a) l2 (pluspf l1 l0))
 ; auto.
apply eqpP1; auto.
apply H' with (y := (l2, (l1, l0))); simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto with arith.
apply
 nzeroP_comp_eqTerm
  with
    (1 := cs)
    (a := plusTerm (A:=A) plusA (n:=n) (plusTerm (A:=A) plusA (n:=n) a1 a0) a);
 auto.
apply (eqT_trans A n) with (y := a0); auto.
apply (plusTerm_eqT2 A plusA n); auto.
apply plusTerm_assoc with (1 := cs); auto.
apply (eqT_sym A n); auto.
Qed.
 
Theorem pluspf_assoc :
 forall p q r,
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 eqP A eqA n (pluspf (pluspf p q) r) (pluspf p (pluspf q r)).
intros p q r H' H'0 H'1.
apply pluspf3_assoc with (l := (p, (q, r))); auto.
Qed.
Hint Resolve pluspf_assoc.
 
Theorem eqp_pluspf_com_l :
 forall p q r,
 eqP A eqA n p q ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r -> eqP A eqA n (pluspf p r) (pluspf q r).
intros p q r H'; generalize r; elim H'; clear r H'.
intros r H' H'0 H'1; rewrite <- pO_pluspf_inv1; auto.
intros ma mb p0 q0 H' H'0 H'1 r H'2 H'3 H'4.
cut (canonical A0 eqA ltM p0);
 [ intros C0 | apply canonical_imp_canonical with (a := ma) ]; 
 auto.
cut (canonical A0 eqA ltM q0);
 [ intros C1 | apply canonical_imp_canonical with (a := mb) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma);
 [ intros nZ0 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := p0) ];
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb);
 [ intros nZ1 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := q0) ];
 auto.
generalize H'4; elim r; clear H'4 r.
intros H'4; rewrite <- pO_pluspf_inv2; rewrite <- pO_pluspf_inv2; auto.
intros a l H'4 H'5.
cut (canonical A0 eqA ltM l);
 [ intros C2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZ2 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := l) ]; 
 auto.
change
  (eqP A eqA n (pluspf (pX ma p0) (pX a l)) (pluspf (pX mb q0) (pX a l)))
 in |- *.
case (ltT_dec A n ltM ltM_dec ma a); [ intros H0; case H0; clear H0 | idtac ];
 intros H0.
cut (ltT ltM mb a); [ intros Or0 | idtac ].
rewrite <- (pluspf_inv2_eq ma a p0 l); auto.
rewrite <- (pluspf_inv2_eq mb a q0 l); auto.
apply eqT_compat_ltTl with (b := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
cut (ltT ltM a mb); [ intros Or0 | idtac ]; auto.
rewrite <- (pluspf_inv1_eq ma a p0 l); auto.
rewrite <- (pluspf_inv1_eq mb a q0 l); auto.
apply eqT_compat_ltTr with (b := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
cut
 (eqTerm eqA (plusTerm (A:=A) plusA (n:=n) ma a)
    (plusTerm (A:=A) plusA (n:=n) mb a)); [ intros eqTerm0 | idtac ]; 
 auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) ma a));
 intros Z0.
rewrite <- (pluspf_inv3a_eq ma a p0 l); auto.
rewrite <- (pluspf_inv3a_eq mb a q0 l); auto.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) ma a);
 auto.
rewrite <- (pluspf_inv3b_eq ma a p0 l); auto.
rewrite <- (pluspf_inv3b_eq mb a q0 l); auto.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
red in |- *; intros H'6; apply Z0.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) mb a);
 auto.
apply plusTerm_comp_l with (1 := cs); auto.
change (eqT mb a) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_comp_l with (1 := cs); auto.
change (eqT mb a) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem eqp_pluspf_com_r :
 forall p q r,
 eqP A eqA n p q ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r -> eqP A eqA n (pluspf r p) (pluspf r q).
intros p q r H'; generalize r; elim H'; clear r H'.
intros r H' H'0 H'1; rewrite <- pO_pluspf_inv2; auto.
intros ma mb p0 q0 H' H'0 H'1 r H'2 H'3 H'4.
cut (canonical A0 eqA ltM p0);
 [ intros C0 | apply canonical_imp_canonical with (a := ma) ]; 
 auto.
cut (canonical A0 eqA ltM q0);
 [ intros C1 | apply canonical_imp_canonical with (a := mb) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma);
 [ intros nZ0 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := p0) ];
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb);
 [ intros nZ1 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := q0) ];
 auto.
generalize H'4; elim r; clear H'4 r.
intros H'4; rewrite <- pO_pluspf_inv1; rewrite <- pO_pluspf_inv1; auto.
intros a l H'4 H'5.
cut (canonical A0 eqA ltM l);
 [ intros C2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZ2 | apply (canonical_nzeroP _ A0 eqA n ltM) with (p := l) ]; 
 auto.
change
  (eqP A eqA n (pluspf (pX a l) (pX ma p0)) (pluspf (pX a l) (pX mb q0)))
 in |- *.
case (ltT_dec A n ltM ltM_dec ma a); [ intros H0; case H0; clear H0 | idtac ];
 intros H0.
cut (ltT ltM mb a); [ intros Or0 | idtac ].
rewrite <- (pluspf_inv1_eq a ma l p0); auto.
rewrite <- (pluspf_inv1_eq a mb l q0); auto.
apply eqT_compat_ltTl with (b := ma); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
cut (ltT ltM a mb); [ intros Or0 | idtac ]; auto.
rewrite <- (pluspf_inv2_eq a ma l p0); auto.
rewrite <- (pluspf_inv2_eq a mb l q0); auto.
apply eqT_compat_ltTr with (b := ma); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
cut
 (eqTerm eqA (plusTerm (A:=A) plusA (n:=n) a ma)
    (plusTerm (A:=A) plusA (n:=n) a mb)); [ intros eqTerm0 | idtac ]; 
 auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a ma));
 intros Z0.
rewrite <- (pluspf_inv3a_eq a ma l p0); auto.
rewrite <- (pluspf_inv3a_eq a mb l q0); auto.
apply (eqT_trans A n) with (y := ma); auto; apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a ma);
 auto.
apply (eqT_sym A n); auto.
rewrite <- (pluspf_inv3b_eq a ma l p0); auto.
rewrite <- (pluspf_inv3b_eq a mb l q0); auto.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
red in |- *; intros H'6; apply Z0.
apply
 zeroP_comp_eqTerm with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a mb);
 auto.
apply plusTerm_comp_r with (1 := cs); auto.
change (eqT a mb) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqT_sym A n); auto.
apply plusTerm_comp_r with (1 := cs); auto.
apply (eqT_sym A n); auto.
change (eqT a mb) in |- *.
apply (eqT_trans A n) with (y := ma); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT _ eqA n); auto.
Qed.
 
Theorem eqp_pluspf_com :
 forall p q r t,
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 canonical A0 eqA ltM t ->
 eqP A eqA n p r -> eqP A eqA n q t -> eqP A eqA n (pluspf p q) (pluspf r t).
intros p q r t H' H'0 H'1 H'2 H'3 H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pluspf r q); auto.
apply eqp_pluspf_com_l; auto.
apply eqp_pluspf_com_r; auto.
Qed.
Hint Resolve eqp_pluspf_com.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition splus : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (pluspf p1 p2); auto.
apply canonical_pluspf; auto.
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
End Pplus.