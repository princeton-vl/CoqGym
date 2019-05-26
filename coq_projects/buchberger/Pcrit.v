(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export Pspoly.
Require Export Pmult.
Section crit.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hSpoly".
Load "hMult".
 
Definition Rminus :
  forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
  list (Term A n) -> list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q r; elim r; clear r.
exact p.
intros b r Rec;
 exact
  (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec Rec
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=a) nZa) q)).
Defined.
 
Theorem minuspf_in :
 forall (p q : list (Term A n)) (a b : Term A n),
 In a p ->
 ltT ltM b a ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM (pX b q) ->
 In a
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (pX b q)).
intros p; elim p; simpl in |- *; auto.
intros q a b H'; elim H'; auto.
intros a l H' q a0 b H'0 H'1 H'2 H'3.
elim H'0; [ intros H'4; rewrite H'4; clear H'0 | intros H'4; clear H'0 ].
change
  (In a0
     (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec 
        (pX a0 l) (pX b q))) in |- *.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
case (ltT_dec A n ltM ltM_dec a b); intros test;
 [ case test; clear test; intros test | idtac ].
absurd (ltT ltM b a0); auto.
apply ltT_not_ltT; auto.
generalize H'4 H'2; elim l; simpl in |- *; auto.
intros H'0; elim H'0; auto.
intros a1 l0 H'0 H'5; elim H'5;
 [ intros H'6; rewrite <- H'6; clear H'5 | intros H'6; clear H'5 ]; 
 auto.
intros H'5; apply (ltT_trans A n ltM os) with (y := a); auto.
apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'0; auto.
change (canonical A0 eqA ltM (pX a l0)) in |- *.
apply canonical_skip_fst with (b := a1); auto.
change
  (In a0
     (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec 
        (pX a l) (pX b q))) in |- *.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
right; auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a); auto.
absurd (ltT ltM b a0); auto.
apply ltT_not_ltT; auto.
apply eqT_compat_ltTr with (b := a); auto.
generalize H'4 H'2; elim l; simpl in |- *; auto.
intros H'0; elim H'0; auto.
intros a1 l0 H'0 H'5; elim H'5;
 [ intros H'6; rewrite <- H'6; clear H'5 | intros H'6; clear H'5 ]; 
 auto.
intros H'5; apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'0; auto.
change (canonical A0 eqA ltM (pX a l0)) in |- *.
apply canonical_skip_fst with (b := a1); auto.
Qed.
 
Theorem minus_is_reduce :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n)
   (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a) (q : list (Term A n)),
 inPolySet A A0 eqA n ltM (pX a q) Q ->
 forall u : Term A n,
 divP A A0 eqA multA divA n u a ->
 forall p : list (Term A n),
 canonical A0 eqA ltM p ->
 In u p ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa)
         (pX a q))).
intros Q a nZa q inP0 u divP0 p; elim p.
intros H' H'0; elim H'0; auto.
intros a0 l H' H'0 H'1; elim H'1;
 [ intros H'2; rewrite H'2; clear H'1 | intros H'2; clear H'1 ]; 
 auto.
change
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
     (pX u l)
     (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec 
        (pX u l)
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa)
           (pX a q)))) in |- *.
apply reducetop with (b := a) (nZb := nZa) (q := q); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec u
            a nZa (pX u l) (pX a q)); auto.
apply spminusf_extend with (1 := cs); auto.
rewrite <- H'2; auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply
 reduce_eqp_com
  with
    (1 := cs)
    (p := pX a0 l)
    (q := pX a0
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a)
                     nZa) (pX a q)))); auto.
apply reduceskip; auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a0); auto.
change
  (eqP A eqA n
     (pX a0
        (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l
           (mults (A:=A) multA (n:=n)
              (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa)
              (pX a q))))
     (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec 
        (pX a0 l)
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa)
           (pX a q)))) in |- *.
simpl in |- *; apply minuspf_inv1 with (1 := cs); auto.
apply eqT_compat_ltTl with (b := u); auto.
inversion divP0; auto.
apply (eqTerm_imp_eqT A eqA n); auto.
generalize H'2 H'0; elim l; simpl in |- *; auto.
intros H'1; elim H'1; auto.
intros a2 l0 H'1 H'3; elim H'3;
 [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; 
 auto.
intros H'5.
apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
intros H'5; apply H'1; auto.
change (canonical A0 eqA ltM (pX a0 l0)) in |- *.
apply canonical_skip_fst with (b := a2); auto.
Qed.
 
Definition divPp : Term A n -> list (Term A n) -> Prop.
intros a p; elim p; clear p.
exact True.
intros b p Rec; exact (divP A A0 eqA multA divA n b a /\ Rec).
Defined.
Hint Resolve divP_inv3.
Hint Resolve divP_inv3.
 
Definition divpf :
  forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
  list (Term A n) -> list (Term A n).
intros a nZa p; elim p; clear p.
exact (pO A n).
intros b p Rec;
 exact
  (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
     (pX (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=a) nZa)
        (pO A n)) Rec).
Defined.
 
Theorem divpf_canonical :
 forall (a : Term A n) (p : list (Term A n))
   (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
 canonical A0 eqA ltM p -> canonical A0 eqA ltM (divpf a nZa p).
intros a p; elim p; simpl in |- *; auto.
intros a0 l H' H'0 H'1.
apply canonical_pluspf; auto.
apply canonicalp1; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a0); auto.
Qed.
Hint Resolve divpf_canonical.
 
Theorem divPp_divpf :
 forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (p : list (Term A n)),
 canonical A0 eqA ltM p ->
 divPp a p -> eqP A eqA n p (mults (A:=A) multA (n:=n) a (divpf a nZa p)).
intros a nZa p; elim p; simpl in |- *; auto.
intros a0 l H' H'0 H'1; elim H'1; intros H'2 H'3; clear H'1.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a
               (pX
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a)
                     nZa) (pO A n)))
            (mults (A:=A) multA (n:=n) a (divpf a nZa l))).
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a
               (pX
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a)
                     nZa) (pO A n))) l).
simpl in |- *.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a)
                     nZa) a) (pO A n)) l).
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX a0 (pO A n)) l).
change
  (eqP A eqA n (pX a0 l)
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a0 (pO A n)) l)) in |- *; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX a0
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pO A n) l)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite pluspf_inv1_eqa; auto.
apply canonicalp1; auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
inversion H'2; auto.
auto.
auto.
Qed.
 
Theorem canonical_Rminus :
 forall (r p q : list (Term A n)) (a : Term A n)
   (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r -> canonical A0 eqA ltM (Rminus a nZa p q r).
intros r; elim r; simpl in |- *; auto.
intros a l nZa p q a0 H'0 H'1 H'2 H'3.
cut (canonical A0 eqA ltM l);
 [ idtac | apply canonical_imp_canonical with (a := a); auto ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ idtac | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
Qed.
Hint Resolve canonical_Rminus.
 
Theorem Rminus_in :
 forall (r p q : list (Term A n)) (a b : Term A n)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b),
 divPp b r ->
 In a p ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM (pX b q) ->
 canonical A0 eqA ltM (pX a r) -> In a (Rminus b nZb p (pX b q) r).
intros r; elim r; simpl in |- *; auto.
intros a l H' p q a0 b nZb H'0 H'1 H'2 H'3 H'4.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q); auto ].
elim H'0; intros H'6 H'7; clear H'0.
apply minuspf_in; auto.
apply H'; auto.
apply canonical_skip_fst with (b := a); auto.
apply eqT_compat_ltTl with (b := a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
inversion H'6; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply canonical_Rminus; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a0); auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)
        (pX b q))) in |- *; auto.
Qed.
 
Theorem Rminus_is_reduceplus :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) 
   (q : list (Term A n)) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
 canonical A0 eqA ltM q ->
 inPolySet A A0 eqA n ltM (pX a q) Q ->
 forall r : list (Term A n),
 canonical A0 eqA ltM r ->
 divPp a r ->
 forall p : list (Term A n),
 canonical A0 eqA ltM p ->
 incl r p ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p
   (Rminus a nZa p (pX a q) r).
intros Q a q nZa Op0 in0 r; elim r; clear r.
simpl in |- *; intros H' H'0 p H'1 H'2; auto.
apply Rstar_0; auto.
intros a0 r1 Rec Op1 divp0 p Op2 incl0.
cut (canonical A0 eqA ltM r1);
 [ intros Cr1 | apply canonical_imp_canonical with (a := a0); auto ].
cut (canonical A0 eqA ltM (pX a q));
 [ intros Caq | apply inPolySet_imp_canonical with (L := Q); auto ].
elim divp0; intros H' H'0; clear divp0.
apply reduceplus_trans with (1 := cs) (y := Rminus a nZa p (pX a q) r1); auto.
apply Rec; auto.
red in |- *; intros p' H; apply incl0; auto with datatypes.
apply
 reduceplus_eqp_com
  with
    (1 := cs)
    (p := Rminus a nZa p (pX a q) r1)
    (q := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (Rminus a nZa p (pX a q) r1)
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a0 (b:=a) nZa)
               (pX a q))); auto.
apply reduce_imp_reduceplus with (1 := cs); auto.
apply minus_is_reduce; auto.
apply Rminus_in; auto with datatypes.
Qed.
 
Definition Dmult :
  forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
  list (Term A n) -> list (Term A n) -> list (Term A n).
intros a nZa p q; elim p; clear p.
exact (pO A n).
intros a1 p1 rec;
 exact
  (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
     (divpf a nZa (mults (A:=A) multA (n:=n) a1 q)) rec).
Defined.
 
Theorem canonical_Dmult :
 forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (p q : list (Term A n)),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q -> canonical A0 eqA ltM (Dmult a nZa p q).
intros a nZa p; elim p; simpl in |- *; auto.
intros a0 l H' q H'0 H'1.
cut (canonical A0 eqA ltM l);
 [ idtac | apply canonical_imp_canonical with (a := a0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
Qed.
Hint Resolve canonical_Dmult.
 
Theorem divp_is_multTerm :
 forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b),
 divP A A0 eqA multA divA n a b ->
 forall p : list (Term A n),
 canonical A0 eqA ltM p ->
 eqP A eqA n
   (mults (A:=A) multA (n:=n)
      (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) p)
   (divpf b nZb (mults (A:=A) multA (n:=n) a p)).
intros a b nZb H'; inversion H'.
intros p; elim p; simpl in |- *; auto.
intros a1 p1 H'0 H'1.
cut (canonical A0 eqA ltM p1);
 [ intros Op0 | apply canonical_imp_canonical with (a := a1) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p1) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (multTerm (A:=A) multA (n:=n) a a1) (b:=b) nZb) 
               (pO A n))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)
               p1)); auto.
cut
 (eqTerm (A:=A) eqA (n:=n)
    (multTerm (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) a1)
    (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
       (multTerm (A:=A) multA (n:=n) a a1) (b:=b) nZb)); 
 auto.
intros H'2.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (multTerm (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)
               a1)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pO A n)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b)
                     nZb) p1))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite pluspf_inv1_eqa; auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)
        (pX a1 p1))) in |- *; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply divTerm_multTerm_r with (1 := cs); auto.
Qed.
 
Theorem Rminus_is_mult :
 forall (r p q : list (Term A n)) (a : Term A n)
   (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 divPp a r ->
 eqP A eqA n (Rminus a nZa p q r)
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
      (Dmult a nZa r q)).
intros r; elim r; clear r; simpl in |- *; auto.
intros p q a nZa H'0 H'1 H'2 H'3; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 auto.
apply minuspf_pO_refl with (1 := cs); auto.
intros a l H' p q a0 nZa0 H'1 H'2 H'3 H'4; elim H'4; intros H'5 H'6;
 clear H'4.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
               (Dmult a0 nZa0 l q))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a0) nZa0)
               q)); [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
               (Dmult a0 nZa0 l q))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a0)
                     nZa0) q))); [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) 
                  (Dmult a0 nZa0 l q)))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a0)
                     nZa0) q))); [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) 
                  (Dmult a0 nZa0 l q))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a
                        (b:=a0) nZa0) q)))); [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (Dmult a0 nZa0 l q)
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a
                        (b:=a0) nZa0) q)))).
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 apply mults_dist_pluspf with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (Dmult a0 nZa0 l q)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a0)
                     nZa0) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply minuspf_comp with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a0) nZa0)
               q) (Dmult a0 nZa0 l q)).
apply pluspf_com with (1 := cs); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply divp_is_multTerm; auto.
auto.
Qed.
 
Theorem divpf_comp :
 forall (a b : Term A n) (p q : list (Term A n)),
 eqP A eqA n p q ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 eqTerm (A:=A) eqA (n:=n) a b ->
 forall (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b),
 eqP A eqA n (divpf a nZa p) (divpf b nZb q).
intros a b p q H'; elim H'; simpl in |- *; auto.
intros ma mb p0 q0 H'0 H'1 H'2 H'3 H'4 H'5 H'6 H'7.
cut (canonical A0 eqA ltM p0);
 [ intros Op1 | apply canonical_imp_canonical with (a := ma); auto ].
cut (canonical A0 eqA ltM q0);
 [ intros Op2 | apply canonical_imp_canonical with (a := mb); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q0); auto ].
auto.
Qed.
 
Theorem Dmult_is_mulpf :
 forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (p q : list (Term A n)),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 eqP A eqA n (Dmult a nZa (mults (A:=A) multA (n:=n) a p) q)
   (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q).
intros a nZa p; elim p; simpl in |- *; auto.
intros a0 l H'0 q H'1 H'2.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a0); auto ].
cut
 (canonical A0 eqA ltM
    (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec l q));
 [ intros Op1 | auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
               (multTerm (A:=A) multA (n:=n) a a0) (b:=a) nZa) q).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply divp_is_multTerm; auto.
apply mults_comp with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n) a0
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) nZa));
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (multTerm (A:=A) multA (n:=n) a0 a) (b:=a) nZa); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem sp_Rminus :
 forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (p q : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX b q) ->
 eqP A eqA n
   (Rminus b nZb
      (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
         (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q))
      (pX b q) (mults (A:=A) multA (n:=n) b p))
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
      (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a p) q)).
intros a b nZb p q H' H'0.
cut (canonical A0 eqA ltM p);
 [ intros Op0 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q);
 [ intros Op1 | apply canonical_imp_canonical with (a := b); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q); auto ];
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n) a q))
            (Dmult b nZb (mults (A:=A) multA (n:=n) b p) (pX b q))).
apply Rminus_is_mult; auto.
generalize Op0; elim p; simpl in |- *; auto.
intros a0 l H'1 H'2; split; auto.
apply divTerm_multTerml with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply H'1.
apply canonical_imp_canonical with (a := a0); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n) a q))
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (pX b q))).
apply minuspf_comp with (1 := cs); auto.
apply Dmult_is_mulpf; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n) a q))
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (pX b q))).
apply minuspf_comp with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n) a q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b p)
               (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) a q)))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b p)
               (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) a q)))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) b p)
                  (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q))));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) a q)))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) b p))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q))));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) a q))
               (mults (A:=A) multA (n:=n) b p))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) b p))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b p)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                     (mults (A:=A) multA (n:=n) b p))
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                     (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)))));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) b p)
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                     (mults (A:=A) multA (n:=n) b p)))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
                  (mults (A:=A) multA (n:=n) b p)
                  (mults (A:=A) multA (n:=n) b p))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pO A n)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q))));
 [ auto | idtac ].
apply eqp_pluspf_com with (1 := cs); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply minuspf_refl with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a q))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a q)
               (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q)));
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
 
Theorem minuspf_spoly_in :
 forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b),
 eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) ->
 forall p q : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 (forall c : Term A n,
  In c p ->
  ltT ltM c (multTerm (A:=A) multA (n:=n) a b) /\
  eqT c
    (multTerm (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) b)) ->
 (forall c : Term A n,
  In c q ->
  ltT ltM c (multTerm (A:=A) multA (n:=n) a b) /\
  eqT c
    (multTerm (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa) a)) ->
 forall c : Term A n,
 In c p ->
 In c (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q).
intros a b nZa nZb H'1 p q; pattern p, q in |- *.
apply (Opm_ind A n ltM ltM_dec); simpl in |- *; intros; auto.
elim H3; auto.
rewrite minuspf_pO_refl_eq; auto.
rewrite <- minuspf_inv2_eq; simpl in |- *; auto.
right; apply H; auto.
apply canonical_imp_canonical with (a := b0); auto.
rewrite <- minuspf_inv1_eq; simpl in |- *; auto.
elim H5; intros H'2; clear H5; auto.
right; apply H; auto.
apply canonical_imp_canonical with (a := a0); auto.
elim (H4 b0); [ intros H'4 H'5 | idtac ]; auto.
elim (H3 a0); [ intros H'6 H'7 | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b0);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q0); auto ].
absurd (eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b));
 auto.
apply eqT_not_ltT with (1 := os); auto.
case (ltT_dec A n ltM ltM_dec (ppc (A:=A) A1 (n:=n) a b) a0); intros test;
 [ case test; clear test; intros test | idtac ].
apply (ltT_trans A n ltM os) with (y := a0); auto.
absurd (ltT ltM a0 (ppc (A:=A) A1 (n:=n) a b)); auto.
apply divP_is_not_order with (1 := cs); auto.
cut (ppcm A A0 eqA multA divA n a b (ppc (A:=A) A1 (n:=n) a b));
 [ intros H'8; inversion H'8 | idtac ]; auto.
apply H6; auto.
apply eqT_nzero_eqT_divP with (c := b0) (nZb := nZa) (1 := cs); auto.
apply eqT_nzero_divP with (nZb := nZb) (1 := cs); auto.
apply ppc_is_ppcm with (1 := cs); auto.
apply eqT_compat_ltTl with (b := a0); auto.
apply (eqT_sym A n); auto.
Qed.
 
Theorem multTerm_or_z_d1 :
 forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (p : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 forall c : Term A n,
 In c (mults (A:=A) multA (n:=n) b p) ->
 ltT ltM c (multTerm (A:=A) multA (n:=n) a b) /\
 eqT c
   (multTerm (A:=A) multA (n:=n)
      (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) b).
intros a b nZb p; elim p; simpl in |- *; auto.
intros H' c H'0; elim H'0; auto.
intros a0 l H' H'0 c H'1; elim H'1;
 [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; 
 auto.
2: apply H'; auto.
2: apply canonical_skip_fst with (b := a0); auto.
split; auto.
apply eqT_compat_ltTr with (b := multTerm (A:=A) multA (n:=n) b a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply multTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) a0 b); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply multTerm_eqT; auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=b) nZb) a0);
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem multTerm_or_z_d2 :
 forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (p : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 forall c : Term A n,
 In c (mults (A:=A) multA (n:=n) b p) ->
 ltT ltM c (multTerm (A:=A) multA (n:=n) b a) /\
 eqT c
   (multTerm (A:=A) multA (n:=n)
      (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb) b).
intros a b H' p; elim p; simpl in |- *; auto.
intros H'0 c H'1; elim H'1.
intros a0 l H'0 H'1 c H'2; elim H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ]; 
 auto.
2: apply H'0; auto.
2: apply canonical_skip_fst with (b := a0); auto.
split; auto.
apply multTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) a0 b); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply multTerm_eqT; auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=b) H') a0);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem in_minuspf_spoly_in :
 forall a b : Term A n,
 eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) ->
 forall p q : list (Term A n),
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX b q) ->
 forall c : Term A n,
 In c (mults (A:=A) multA (n:=n) b p) ->
 In c
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q)).
intros a b H' p q H'0 H'1 c H'2.
cut (canonical A0 eqA ltM p);
 [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM q);
 [ intros Op1 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; 
 auto.
apply minuspf_spoly_in with (a := a) (b := b) (nZa := Z0) (nZb := Z1); auto.
intros c0 H'6.
apply multTerm_or_z_d1 with (p := p); auto.
intros c0 H'6.
apply multTerm_or_z_d2 with (p := q); auto.
Qed.
 
Theorem divPp_mults1 :
 forall a : Term A n,
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 forall p : list (Term A n),
 (forall b : Term A n, In b p -> ~ zeroP (A:=A) A0 eqA (n:=n) b) ->
 divPp a (mults (A:=A) multA (n:=n) a p).
intros a H' p; elim p; simpl in |- *; auto.
Qed.
 
Theorem spoly_Reduce :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n),
 eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) ->
 forall p q : list (Term A n),
 inPolySet A A0 eqA n ltM (pX b q) Q ->
 canonical A0 eqA ltM (pX a p) ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q))
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
      (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a p) q)).
intros Q a b H' p q H'0 H'1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros nZb
 | apply canonical_nzeroP with (ltM := ltM) (p := q);
    apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (canonical A0 eqA ltM p);
 [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM (pX b q));
 [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p) ]; 
 auto.
cut (canonical A0 eqA ltM q);
 [ intros Op2 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; 
 auto.
apply
 reduceplus_eqp_com
  with
    (1 := cs)
    (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q))
    (q := Rminus b nZb
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n) b p)
               (mults (A:=A) multA (n:=n) a q)) (pX b q)
            (mults (A:=A) multA (n:=n) b p)); auto.
apply Rminus_is_reduceplus; auto.
apply divPp_mults1; auto.
intros b0 H'2; apply (canonical_imp_in_nzero A A0 eqA n ltM p); auto.
red in |- *; intros a0 H'2; apply in_minuspf_spoly_in; auto.
apply sp_Rminus; auto; auto.
Qed.
 
Theorem spoly_reduceplus_pO :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 inPolySet A A0 eqA n ltM q Q ->
 canonical A0 eqA ltM p ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p q) 
   (pO A n).
intros Q p; elim p; auto.
simpl in |- *; auto.
intros; apply Rstar_0; auto.
intros a1 p1 H' q H'0 H'1.
cut (canonical A0 eqA ltM p1);
 [ intros Op0 | apply canonical_imp_canonical with (a := a1) ]; 
 auto.
cut (canonical A0 eqA ltM q);
 [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p1) ]; 
 auto.
apply
 reduceplus_trans
  with
    (1 := cs)
    (y := multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 q); 
 auto.
generalize Op1 H'0; case q; clear Op1 H'0 q.
intros H'0 H'2; elim (not_nil_in_polySet A A0 eqA n ltM Q); auto.
intros b1 q1 H'0 H'2.
cut (canonical A0 eqA ltM q1);
 [ intros Op2 | apply canonical_imp_canonical with (a := b1) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b1);
 [ intros nZb1 | apply canonical_nzeroP with (ltM := ltM) (p := q1) ]; 
 auto.
apply
 reduceplus_eqp_com
  with
    (1 := cs)
    (p := multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec 
            (pX a1 p1) (pX b1 q1))
    (q := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec 
               (pX a1 p1) (pX b1 q1))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (multTerm (A:=A) multA (n:=n) a1 b1) (b:=b1) nZb1)
               (pX b1 q1))); auto.
apply reduce_imp_reduceplus with (1 := cs); auto.
apply minus_is_reduce; auto.
apply in_multpf_head; auto.
cut
 (eqTerm (A:=A) eqA (n:=n)
    (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
       (multTerm (A:=A) multA (n:=n) a1 b1) (b:=b1) nZb1) a1);
 [ intros Eq0 | auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec 
               (pX a1 p1) (pX b1 q1))
            (mults (A:=A) multA (n:=n) a1 (pX b1 q1))); 
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a1 (pX b1 q1))
               (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1
                  (pX b1 q1)))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))); 
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1
                  (pX b1 q1)) (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))); 
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a1 (pX b1 q1))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1))
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n) a1 (pX b1 q1))
               (mults (A:=A) multA (n:=n) a1 (pX b1 q1)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec p1 (pX b1 q1))
            (pO A n)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply minuspf_refl with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n) a1
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b1 (b:=b1) nZb1));
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := multTerm (A:=A) multA (n:=n) a1 (T1 A1 n)); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem fspoly_Reduceplus_pO :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n),
 eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) ->
 forall p q : list (Term A n),
 inPolySet A A0 eqA n ltM (pX b q) Q ->
 inPolySet A A0 eqA n ltM (pX a p) Q ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q))
   (pO A n).
intros Q a b H' p q H'0 H'1.
cut (canonical A0 eqA ltM (pX a p));
 [ intros Op0 | apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (canonical A0 eqA ltM (pX b q));
 [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (canonical A0 eqA ltM p);
 [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM q);
 [ intros Op3 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; 
 auto.
apply
 reduceplus_trans
  with
    (1 := cs)
    (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec (pX a p) q));
 auto.
apply spoly_Reduce; auto.
apply
 reduceplus_eqp_com
  with
    (1 := cs)
    (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (multpf A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (pX a p)))
    (q := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (pO A n)); auto.
apply reduceplus_mults with (1 := cs); auto.
apply spoly_reduceplus_pO; auto.
apply mults_comp with (1 := cs); auto.
apply multpf_com with (1 := cs); auto.
Qed.
 
 
Theorem spoly_Reducestar_pO :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n),
 eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) ->
 forall (p q : list (Term A n)) (Cpxb : canonical A0 eqA ltM (pX b q))
   (Cpxa : canonical A0 eqA ltM (pX a p)),
 inPolySet A A0 eqA n ltM (pX b q) Q ->
 inPolySet A A0 eqA n ltM (pX a p) Q ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec 
      (pX a p) (pX b q) Cpxa Cpxb) (pO A n).
intros Q a b H' p q Cpxb Cpxa H'0 H'1.
cut (canonical A0 eqA ltM p);
 [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM q);
 [ intros Op3 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZa | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZb | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b));
 [ intros nZppab | idtac ]; auto.
apply
 reduceplus_mults_inv
  with
    (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (multTerm (A:=A) multA (n:=n) a b) (b:=
            ppc (A:=A) A1 (n:=n) a b) nZppab)
    (1 := cs); auto.
apply divP_on_eqT_eqT; auto.
apply (eqT_sym A n); auto.
2: apply spolyf_canonical with (1 := cs); auto.
2: apply canonical_nzeroP with (ltM := ltM) (p := q); auto.
2: apply canonical_nzeroP with (ltM := ltM) (p := p); auto.
apply
 reduceplus_eqp_com
  with
    (1 := cs)
    (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n) b p) (mults (A:=A) multA (n:=n) a q))
    (q := pO A n); auto.
apply fspoly_Reduceplus_pO; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
               (multTerm (A:=A) multA (n:=n) a b)
               (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (multTerm (A:=A) multA (n:=n) a b)
                  (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (multTerm (A:=A) multA (n:=n) a b)
                  (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (multTerm (A:=A) multA (n:=n) a b)
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa)) p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (multTerm (A:=A) multA (n:=n) a b)
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb)) q)); 
 auto.
apply minuspf_comp with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divP_comp_ppc0 with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divP_comp_ppc1 with (1 := cs); auto.
apply minuspf_comp with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 apply mults_comp_minuspf with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply spolyf_def with (1 := cs); auto.
Qed.
 
Theorem spoly_Reducestar_ppc :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n),
 eqT (ppc (A:=A) A1 (n:=n) a b) (multTerm (A:=A) multA (n:=n) a b) ->
 forall (p q : list (Term A n)) (Cpxb : canonical A0 eqA ltM (pX b q))
   (Cpxa : canonical A0 eqA ltM (pX a p)),
 inPolySet A A0 eqA n ltM (pX b q) Q ->
 inPolySet A A0 eqA n ltM (pX a p) Q ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec 
      (pX a p) (pX b q) Cpxa Cpxb) (pO A n).
intros Q a b H' p q Cpxb Cpxa H'0 H'1.
apply reducestar0; auto.
apply spoly_Reducestar_pO; auto.
apply pO_irreducible; auto.
Qed.
End crit.