(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : reduction                                           
                                                                           
          Laurent Thery May 97 (revised April 01)                            
                                                                           
  ****************************************************************************)
Require Export Pspminus.
Section Preduce.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hSpminus".
 
Inductive inPolySet : list (Term A n) -> list (poly A0 eqA ltM) -> Prop :=
  | incons :
      forall (a : Term A n) (p : list (Term A n))
        (H : canonical A0 eqA ltM (pX a p)) (P : list (poly A0 eqA ltM)),
      inPolySet (pX a p)
        (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) 
           (pX a p) H :: P)
  | inskip :
      forall (a : poly A0 eqA ltM) (p : list (Term A n))
        (P : list (poly A0 eqA ltM)), inPolySet p P -> inPolySet p (a :: P).
Hint Resolve incons inskip.
 
Lemma inPolySet_imp_canonical :
 forall (p : list (Term A n)) (L : list (poly A0 eqA ltM)),
 inPolySet p L -> canonical A0 eqA ltM p.
intros p L H'; elim H'; auto.
Qed.
Hint Resolve inPolySet_imp_canonical.
 
Lemma not_nil_in_polySet_elm :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 inPolySet p Q -> p <> pO A n.
intros Q p H'; elim H'; auto.
intros a p0 H'0 H'1; red in |- *; intros H'2; inversion H'2.
Qed.
 
Theorem not_nil_in_polySet :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 ~ inPolySet (pO A n) Q.
intros Q H'; red in |- *; intros H'0.
lapply (not_nil_in_polySet_elm Q (pO A n));
 [ intros H'3; apply H'3 || elim H'3 | idtac ]; auto.
Qed.
 
Lemma inPolySet_is_pX :
 forall (p : list (Term A n)) (L : list (poly A0 eqA ltM)),
 inPolySet p L ->
 exists a : Term A n, (exists q : list (Term A n), p = pX a q).
intros p L H'; elim H'; auto.
intros a p0 H'0 H'1; exists a; exists p0; auto.
Qed.
 
Inductive reduce (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> list (Term A n) -> Prop :=
  | reducetop :
      forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
        (p q r : list (Term A n)),
      inPolySet (pX b q) Q ->
      divP A A0 eqA multA divA n a b ->
      eqP A eqA n
        (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
           b nZb p q) r -> reduce Q (pX a p) r
  | reduceskip :
      forall (a b : Term A n) (p q : list (Term A n)),
      reduce Q p q ->
      eqTerm (A:=A) eqA (n:=n) a b -> reduce Q (pX a p) (pX b q).
Hint Resolve reduceskip.
 
Lemma pO_reduce :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 ~ reduce Q (pO A n) p.
intros Q p; red in |- *; intros H'; inversion H'; auto.
Qed.
 
Theorem reduce_in_pO :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 inPolySet p Q -> reduce Q p (pO A n).
intros Q p; case p; simpl in |- *; auto.
intros H'; elim (inPolySet_is_pX (pO A n) Q);
 [ intros a E; elim E; intros q E0; inversion E0 | idtac ]; 
 auto.
intros a l H'.
cut (canonical A0 eqA ltM (pX a l)); [ intros Op0 | idtac ].
cut (canonical A0 eqA ltM l);
 [ intros Op1 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Nza | idtac ].
cut
 (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a Nza l
    l = pO A n).
intros H'0; rewrite <- H'0.
change
  (reduce Q (pX a l)
     (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a
        Nza l l)) in |- *.
apply reducetop with (b := a) (nZb := Nza) (q := l); auto.
apply divP_on_eqT with (1 := cs); auto.
cut
 (eqP A eqA n
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a
       Nza l l) (pO A n)).
intros H'0; inversion H'0; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) Nza)
               l)); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l
            (mults (A:=A) multA (n:=n) (T1 A1 n) l)); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec l l);
 auto.
apply minuspf_refl with (1 := cs); auto.
apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
Qed.
 
Theorem ltP_reduce :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduce Q p q -> canonical A0 eqA ltM p -> ltP (A:=A) (n:=n) ltM q p.
intros Q p q H'; elim H'; auto.
2: intros a b p0 q0 H'0 H'1 H'2 H'3; apply ltP_tl; auto.
2: apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
2: apply H'1; try apply canonical_imp_canonical with (a := a); auto.
intros a b nZb p0; case p0; auto.
intros q0 r H'0 H'1 H'2 H'3.
change (ltP (A:=A) (n:=n) ltM r (pX a (pO A n))) in |- *.
apply (canonical_pX_ltP A A0 eqA); auto.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := pX a
            (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
               ltM_dec a b nZb (pO A n) q0)); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
intros t l q0 r H'0 H'1 H'2 H'3; apply ltP_trans with (y := pX a (pO A n));
 auto.
apply (canonical_pX_ltP A A0 eqA); auto.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := pX a
            (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
               ltM_dec a b nZb (pX t l) q0)); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
change (ltP (A:=A) (n:=n) ltM (pX a (pO A n)) (pX a (pX t l))) in |- *; auto.
Qed.
 
Theorem canonical_reduce :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduce Q p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q.
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 H'3.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            b nZb p0 q0); auto.
apply canonical_spminusf with (1 := cs); auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
intros a b p0 q0 H'0 H'1 H'2 H'3.
apply eqp_imp_canonical with (1 := cs) (p := pX a q0); auto.
cut (canonical A0 eqA ltM p0);
 [ intros C1 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
apply ltP_pX_canonical; auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
apply ltP_trans with (y := p0); auto.
apply ltP_reduce with (Q := Q); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
Qed.
 
Theorem reduce_eqp_com :
 forall (Q : list (poly A0 eqA ltM)) (p q r s : list (Term A n)),
 reduce Q p q ->
 canonical A0 eqA ltM p -> eqP A eqA n p r -> eqP A eqA n q s -> reduce Q r s.
intros Q p q r s H'; generalize r s; clear r s; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 r0 s H'3 H'4 H'5.
inversion_clear H'4.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            b nZb p0 q0); auto.
cut (canonical A0 eqA ltM p0);
 [ intros Cp0 | apply canonical_imp_canonical with (a := a); auto ].
apply eqp_spminusf_com with (1 := cs); auto.
apply eqp_imp_canonical with (1 := cs) (p := p0); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_eqTerm_comp with (1 := cs) (a := a); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (2 := H'5); auto.
intros a b p0 q0 H'0 H'1 H'2 r s H'3 H'4 H'5.
inversion_clear H'4.
inversion_clear H'5.
apply reduceskip; auto.
apply H'1; auto.
apply canonical_imp_canonical with (a := a); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := a); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
Qed.
 
Theorem reduce_inv :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (p q : list (Term A n)),
 reduce Q (pX a p) (pX b q) ->
 eqTerm (A:=A) eqA (n:=n) a b ->
 canonical A0 eqA ltM (pX a p) -> reduce Q p q.
intros Q a b p q H'; inversion_clear H'; auto.
intros eq Cap.
elim (not_double_canonical A A0 eqA n ltM) with (a := b) (p := q); auto.
apply
 eqp_imp_canonical
  with
    (p := pX b
            (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
               ltM_dec a b0 nZb p q0))
    (1 := cs); auto.
apply (canonical_pX_eqT A A0 eqA n ltM) with (a := a); auto.
apply canonical_spminusf_full_t with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := a); auto.
apply canonical_nzeroP with (p := p) (ltM := ltM); auto.
Qed.
 
Theorem reducetop_sp :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)),
 inPolySet (pX b q) Q ->
 divP A A0 eqA multA divA n a b ->
 reduce Q (pX a p)
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p q).
intros Q a b nZb p q H' H'0.
apply reducetop with (b := b) (nZb := nZb) (q := q); auto.
Qed.
Hint Resolve reducetop_sp.
 
Theorem reduce_inv2 :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduce Q p q ->
 canonical A0 eqA ltM p ->
 exists x : list (Term A n),
   (exists a : Term A n,
      ~ zeroP (A:=A) A0 eqA (n:=n) a /\
      inPolySet x Q /\
      canonical A0 eqA ltM x /\
      eqP A eqA n q
        (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
           (mults (A:=A) multA (n:=n) a x))).
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 r H'0 H'1 H'2 H'3; cut (canonical A0 eqA ltM (pX b q0));
 [ intros C1 | apply inPolySet_imp_canonical with (L := Q); auto ];
 exists (pX b q0);
 exists (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb); 
 split; [ idtac | split; [ idtac | split; [ idtac | idtac ] ] ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            b nZb p0 q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            b nZb (pX a p0) (pX b q0)); auto.
apply spminusf_extend with (1 := cs); auto.
intros a b p0 q0 H'0 H'1 H'2 H'3.
cut (canonical A0 eqA ltM p0);
 [ intros Op1 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM (pX a q0));
 [ intros Op2 | apply canonical_reduce with (Q := Q) (p := pX a p0) ]; 
 auto.
cut (canonical A0 eqA ltM q0);
 [ intros Op3 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
elim H'1;
 [ intros x E; elim E; intros a0 E0; elim E0; intros H'4 H'5; elim H'5;
    intros H'6 H'7; elim H'7; intros H'8 H'9; clear H'7 H'5 E0 E H'1
 | clear H'1 ]; auto.
exists x; exists a0; split; [ idtac | split; [ idtac | split ] ]; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := pX a q0);
 [ auto | apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n) ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX a p0)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a0 x))); 
 [ auto | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z0 | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pX a (pO A n)) p0)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n) a0 x))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs);
 auto.
apply plusTerm_is_pX with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX a (pO A n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p0
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n) a0 x)))); 
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX a (pO A n))
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p0
               (mults (A:=A) multA (n:=n) a0 x))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX a (pO A n)) q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply plusTerm_is_pX with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := q0); auto.
Qed.
 
Theorem mults_eqp_inv :
 forall (a : Term A n) (p q : list (Term A n)),
 eqP A eqA n (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q) ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n p q.
intros a p; elim p; auto.
intros q; case q; simpl in |- *; auto.
intros t l H'; inversion_clear H'; auto.
intros a0 l H' q; case q; simpl in |- *; auto.
intros H'0; inversion_clear H'0; auto.
intros t l0 H'0; inversion_clear H'0; auto.
intros H'1.
change (eqP A eqA n (pX a0 l) (pX t l0)) in |- *.
apply eqpP1; auto.
apply multTerm_eqTerm_inv with (1 := cs) (a := a); auto.
Qed.
 
Theorem reduce_mults_invf :
 forall (a : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a),
 eqT a (T1 A1 n) ->
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 canonical A0 eqA ltM p ->
 reduce Q (mults (A:=A) multA (n:=n) a p) q ->
 reduce Q p
   (mults (A:=A) multA (n:=n)
      (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) (T1 A1 n) (b:=a) nZa) q).
intros a H' eq0 Q p; elim p; auto.
simpl in |- *; intros q H'0 H'1; inversion_clear H'1; auto.
intros a0 l H'0 q H'1 H'2.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
generalize H'0 H'1; inversion_clear H'2; clear H'0 H'1; auto.
intros H'0 H'1.
cut (canonical A0 eqA ltM (pX b q0));
 [ intros Op1 | apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (canonical A0 eqA ltM q0);
 [ intros Op2 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (divP A A0 eqA multA divA n a0 b); [ intros d0 | idtac ].
apply
 reduce_eqp_com
  with
    (p := pX a0 l)
    (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
            a0 b nZb l q0); auto.
apply mults_eqp_inv with (a := a); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (multTerm (A:=A) multA (n:=n) a
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
                  (T1 A1 n) (b:=a) H')) q); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := mults (A:=A) multA (n:=n) (T1 A1 n) q); 
 auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := q); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
            (multTerm (A:=A) multA (n:=n) a a0) b nZb
            (mults (A:=A) multA (n:=n) a l) q0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply spminusf_multTerm with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (multTerm (A:=A) multA (n:=n) a (T1 A1 n)) (b:=a) H'); 
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=a) H');
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divTerm_multTerm_l with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply
 eqT_nzero_eqT_divP
  with (1 := cs) (c := multTerm (A:=A) multA (n:=n) a a0) (nZb := nZb); 
 auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0);
 auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply (eqT_sym A n); auto.
intros H'0 H'1.
change
  (reduce Q (pX a0 l)
     (pX
        (multTerm (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
              (T1 A1 n) (b:=a) H') b)
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
              (T1 A1 n) (b:=a) H') q0))) in |- *.
apply reduceskip; auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
               (T1 A1 n) (b:=a) H') (multTerm (A:=A) multA (n:=n) a a0));
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n)
            (multTerm (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
                  (T1 A1 n) (b:=a) H') a) a0); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); 
 auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply multTerm_assoc with (1 := cs); auto.
Qed.
 
Theorem reduce_mults :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p q : list (Term A n)),
 reduce Q p q ->
 canonical A0 eqA ltM p ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 reduce Q (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a q).
intros Q a p q H'; generalize a; elim H'; clear a H'; auto.
simpl in |- *; auto.
intros a b nZb p0 q0 r H' H'0 H'1 a0 H'2 H'3.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a));
 [ intros nZ0 | idtac ]; auto.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divTerm_def with (nZb := nZb); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n)
            (multTerm (A:=A) multA (n:=n) a0
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb))
            b); [ auto | idtac ].
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multTerm (A:=A) multA (n:=n) a0
            (multTerm (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)
               b)); [ auto | idtac ].
apply multTerm_assoc with (1 := cs); auto.
apply eqTerm_multTerm_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply divTerm_multTerm_l with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) a0
            (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
               ltM_dec a b nZb p0 q0)); auto.
apply spminusf_multTerm with (1 := cs); auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := b); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply nzeroP_multTerm with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
intros a b p0 q0 H' H'0 H'1 a0 H'2 H'3.
simpl in |- *; apply reduceskip; auto.
apply H'0; auto.
apply canonical_imp_canonical with (a := a); auto.
Qed.
Hint Resolve reduce_mults.
 
Theorem reduce_mults_inv_lem :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduce Q p q ->
 forall r : list (Term A n),
 canonical A0 eqA ltM r ->
 p = mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r ->
 reduce Q r
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q).
intros Q p q H'; elim H'; clear H'; auto.
2: intros a b p0 q0 H' H'0 H'1 r; case r; auto.
2: intros H'2 H'3; inversion_clear H'3; auto.
2: intros a0 l H'2 H'3.
2: change
     (reduce Q (pX a0 l)
        (pX
           (multTerm (A:=A) multA (n:=n)
              (invTerm (A:=A) invA (n:=n) (T1 A1 n)) b)
           (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
              q0))) in |- *.
2: apply reduceskip; auto.
2: apply H'0; auto.
2: apply canonical_imp_canonical with (a := a0); auto.
2: inversion_clear H'3; auto.
2: apply
    (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
     with
       (y := multTerm (A:=A) multA (n:=n)
               (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a); 
    auto.
2: replace a with
    (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a0);
    [ idtac | inversion H'3 ]; auto.
2: apply
    (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
     with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); 
    auto.
2: apply
    (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
     with
       (y := multTerm (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))) a0);
    apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a b nZb p0 q0 r H' H'0 H'1 r0; case r0; auto.
intros; discriminate.
intros a0 l H'2 H'3.
change
  (pX a p0 =
   pX
     (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a0)
     (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) l))
 in H'3.
cut (canonical A0 eqA ltM l);
 try apply canonical_imp_canonical with (a := a0); 
 auto; intros C0.
change (reduce Q (pX a0 l) (mults multA (invTerm invA (T1 A1 n)) r)) in |- *.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply divP_eqT with (1 := cs) (a := a); auto.
rewrite pX_invl with (1 := H'3); auto.
apply (eqT_sym A n);
 apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0);
 auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
cut (canonical A0 eqA ltM (pX b q0));
 try apply inPolySet_imp_canonical with (L := Q); auto; 
 intros C1.
cut (canonical A0 eqA ltM q0);
 try apply canonical_imp_canonical with (a := b); auto; 
 intros C2.
cut (canonical A0 eqA ltM (pX a p0)); [ intros C3 | idtac ]; auto.
cut (canonical A0 eqA ltM p0);
 try apply canonical_imp_canonical with (a := a); auto; 
 intros C4.
cut (divP A A0 eqA multA divA n a0 b); [ intros divP0 | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
               ltM_dec a b nZb p0 q0)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with
     (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
             (multTerm (A:=A) multA (n:=n)
                (invTerm (A:=A) invA (n:=n) (T1 A1 n)) a) b nZb
             (mults (A:=A) multA (n:=n)
                (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p0) q0); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply spminusf_multTerm with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
            a0 b nZb
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               p0) q0); auto.
apply eqTerm_spminusf_com with (1 := cs); auto.
rewrite pX_invl with (1 := H'3); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (multTerm (A:=A) multA (n:=n)
       (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
          (invTerm (A:=A) invA (n:=n) (T1 A1 n))) a0); 
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (multTerm (A:=A) multA (n:=n) (T1 A1 n) a0); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply divP_eqT with (1 := cs) (a := a); auto.
apply (eqT_trans A n) with (multTerm (A:=A) multA (n:=n) (T1 A1 n) a); auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := invTerm (A:=A) invA (n:=n) a);
 auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) (T1 A1 n) a));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_spminusf_com with (1 := cs); auto.
rewrite pX_invr with (1 := H'3); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (multTerm (A:=A) multA (n:=n)
               (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (invTerm (A:=A) invA (n:=n) (T1 A1 n))) l); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divP_eqT with (1 := cs) (a := a); auto.
rewrite pX_invl with (1 := H'3); auto.
apply (eqT_sym A n);
 apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a0);
 auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := invTerm (A:=A) invA (n:=n) a);
 auto.
apply nZero_invTerm_nZero with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
rewrite pX_invl with (1 := H'3); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (multTerm (A:=A) multA (n:=n)
       (invTerm (A:=A) invA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))) a0);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply mult_invTerm_com with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (multTerm (A:=A) multA (n:=n) (T1 A1 n) a0);
 apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
rewrite H'3;
 change
   (canonical A0 eqA ltM
      (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
         (pX a0 l))) in |- *; auto.
Qed.
 
Theorem reduce_mults_invr :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduce Q
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p) q ->
 canonical A0 eqA ltM p ->
 reduce Q p
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) q).
intros Q p q H' H'0.
apply
 reduce_mults_inv_lem
  with
    (p := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p);
 auto.
Qed.
 
Definition irreducible (Q : list (poly A0 eqA ltM)) 
  (p : list (Term A n)) := forall q : list (Term A n), ~ reduce Q p q.
 
Lemma irreducible_inv_px_l :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 irreducible Q (pX a p) -> irreducible Q (pX a (pO A n)).
unfold irreducible in |- *.
intros Q a p H' H'0 q; red in |- *; intros H'1.
inversion_clear H'1.
apply 
 H'0
   with
     (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
             a b nZb p q0); auto.
inversion_clear H; auto.
Qed.
 
Lemma pO_irreducible :
 forall Q : list (poly A0 eqA ltM), irreducible Q (pO A n).
unfold irreducible in |- *; auto.
intros Q q; red in |- *; intros H'; inversion H'.
Qed.
Hint Resolve pO_irreducible.
 
Theorem irreducible_eqp_com :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 irreducible Q p ->
 canonical A0 eqA ltM p -> eqP A eqA n p q -> irreducible Q q.
unfold irreducible in |- *.
intros Q p q H' H'0 H'1 q0; red in |- *; intros H'2.
apply H' with (q := q0); auto.
apply reduce_eqp_com with (p := q) (q := q0); auto.
apply eqp_imp_canonical with (1 := cs) (p := p); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Inductive pickinSetp :
Term A n -> list (Term A n) -> list (poly A0 eqA ltM) -> Prop :=
  | pickinSeteqp :
      forall (a b : Term A n) (p : list (Term A n))
        (H : canonical A0 eqA ltM (pX b p)) (P : list (poly A0 eqA ltM)),
      divP A A0 eqA multA divA n a b ->
      pickinSetp a (pX b p)
        (exist (fun l0 : list (Term A n) => canonical A0 eqA ltM l0) 
           (pX b p) H :: P)
  | pickinSetskip :
      forall (a b : Term A n) (p : list (Term A n)) 
        (q : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)),
      pickinSetp a p P -> pickinSetp a p (q :: P).
Hint Resolve pickinSeteqp pickinSetskip.
 
Lemma pickin_is_pX :
 forall (a : Term A n) (p : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 pickinSetp a p Q ->
 exists b : Term A n, (exists q : list (Term A n), p = pX b q).
intros a p Q H'; elim H'; auto.
intros a0 b p0 H'0 H'1 H'2; exists b; exists p0; auto.
Qed.
 
Inductive reducehead (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> list (Term A n) -> Prop :=
    reduceheadO :
      forall (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
        (p q : list (Term A n)),
      pickinSetp a (pX b q) Q ->
      reducehead Q (pX a p)
        (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
           b nZb p q).
Hint Resolve reduceheadO.
 
Lemma pick_inv_in :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)),
 pickinSetp a p Q -> inPolySet p Q.
intros Q a p H'; elim H'; auto.
Qed.
 
Lemma pick_inv_eqT_lem :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)),
 pickinSetp a p Q ->
 forall (b : Term A n) (q : list (Term A n)),
 p = pX b q -> divP A A0 eqA multA divA n a b.
intros Q a p H'; elim H'; auto.
intros a0 b p0 H'0 H'1 H'2 b0 q H'3; injection H'3; auto.
intros H'4 H'5; rewrite <- H'5; auto.
Qed.
 
Lemma pick_inv_eqT :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n) (p q : list (Term A n)),
 pickinSetp a (pX b q) Q -> divP A A0 eqA multA divA n a b.
intros Q a b H' q H'0.
apply pick_inv_eqT_lem with (Q := Q) (p := pX b q) (q := q); auto.
Qed.
 
Theorem reducehead_imp_reduce :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reducehead Q p q -> reduce Q p q.
intros Q p q H'; elim H'; auto.
intros a b nZb p0 q0 H'0.
apply reducetop with (b := b) (nZb := nZb) (q := q0); auto.
apply pick_inv_in with (a := a); auto.
apply pick_inv_eqT with (Q := Q) (q := q0); auto.
Qed.
 
Definition s2p : poly A0 eqA ltM -> list (Term A n).
intros H'; elim H'.
intros x H'0; exact x.
Defined.
 
Theorem In_inp_inPolySet :
 forall (Q : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p Q -> ~ eqP A eqA n (s2p p) (pO A n) -> inPolySet (s2p p) Q.
intros Q; elim Q; simpl in |- *; auto.
intros p H'; elim H'.
intros a l H' p H'0; elim H'0;
 [ intros H'1; rewrite H'1; clear H'0 | intros H'1; clear H'0 ]; 
 auto.
case p; simpl in |- *; auto.
intros x; case x; simpl in |- *; auto.
intros c H'0; elim H'0; auto.
intros t l0 c H;
 change (inPolySet (pX t l0) (exist (canonical A0 eqA ltM) (pX t l0) c :: l))
  in |- *; apply incons.
Qed.
 
Theorem in_inPolySet :
 forall (P : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p P -> ~ eqP A eqA n (s2p p) (pO A n) -> inPolySet (s2p p) P.
intros P; elim P; auto.
intros p H'; inversion H'.
simpl in |- *.
intros a l H' p H'0; elim H'0;
 [ intros H'1; rewrite <- H'1; clear H'0 | intros H'1; clear H'0 ]; 
 auto.
case a; simpl in |- *.
intros x; case x; auto.
intros c H'0; elim H'0; auto.
intros t l0 c H;
 change (inPolySet (pX t l0) (exist (canonical A0 eqA ltM) (pX t l0) c :: l))
  in |- *; apply incons.
Qed.
 
Theorem inPolySet_inv0 :
 forall (P : list (poly A0 eqA ltM)) (p : list (Term A n)),
 inPolySet p P -> ~ eqP A eqA n p (pO A n).
intros P p H'; elim H'; auto.
intros a p0 H'0 H'1; red in |- *; intros H'2; inversion H'2.
Qed.
 
Theorem inPolySet_inv1 :
 forall (P : list (poly A0 eqA ltM)) (p : list (Term A n)),
 inPolySet p P -> exists q : poly A0 eqA ltM, In q P /\ p = s2p q.
intros P p H'; elim H'; auto.
intros a p0 H P0.
exists (exist (canonical A0 eqA ltM) (a :: p0) H); split; simpl in |- *; auto.
intros a p0 P0 H'0 H'1; elim H'1; intros q E; elim E; intros H'2 H'3;
 clear E H'1.
exists q; split; simpl in |- *; auto.
Qed.
 
Theorem Incl_inp_inPolySet :
 forall P Q : list (poly A0 eqA ltM),
 incl P Q -> forall p : list (Term A n), inPolySet p P -> inPolySet p Q.
intros P Q H' p H'0; auto.
elim (inPolySet_inv1 P p);
 [ intros q E; elim E; intros H'4 H'5; clear E | idtac ]; 
 auto.
rewrite H'5.
apply in_inPolySet; auto.
rewrite <- H'5; auto.
apply inPolySet_inv0 with (P := P); auto.
Qed.
End Preduce.