(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export Preducestar.
Require Export LetP.
Section Pspoly.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hReducestar".
 
Definition spolyf :
  forall (p q : list (Term A n)) (Cp : canonical A0 eqA ltM p)
    (Cq : canonical A0 eqA ltM q), list (Term A n).
intros p1; case p1.
intros p2 H' H'0; exact (pO A n).
intros a p11 p2; case p2.
intros H' H'0; exact (pO A n).
intros b p22 H' H'0.
apply LetP with (A := Term A n) (h := ppc (A:=A) A1 (n:=n) a b).
intros u H'1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZa | apply canonical_nzeroP with (ltM := ltM) (p := p11); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros nZb | apply canonical_nzeroP with (ltM := ltM) (p := p22); auto ].
exact
 (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
    (mults (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=a) nZa) p11)
    (mults (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) u (b:=b) nZb) p22)).
Defined.
 
Theorem spolyf_canonical :
 forall (p q : list (Term A n)) (Cp : canonical A0 eqA ltM p)
   (Cq : canonical A0 eqA ltM q), canonical A0 eqA ltM (spolyf p q Cp Cq).
intros p; case p; simpl in |- *; auto.
intros a l q; case q; unfold LetP in |- *; simpl in |- *; auto.
intros a0 l0 H' H'0.
cut (canonical A0 eqA ltM l0);
 [ intros Op1 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
cut (canonical A0 eqA ltM l);
 [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := l0) ]; 
 auto.
Qed.
Hint Resolve spolyf_canonical.
 
Theorem spolyf_pO :
 forall (a : list (Term A n)) (Ca : canonical A0 eqA ltM a),
 eqP A eqA n (spolyf a a Ca Ca) (pO A n).
intros a; case a; simpl in |- *; unfold LetP in |- *; auto.
intros; apply minuspf_refl with (1 := cs); auto.
Qed.
 
Theorem spolyf_com :
 forall (a b : list (Term A n)) (Ca : canonical A0 eqA ltM a)
   (Cb : canonical A0 eqA ltM b),
 eqP A eqA n (spolyf a b Ca Cb)
   (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
      (spolyf b a Cb Ca)).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 l a1 l0 Cpxa0 Cpxa1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros nZa0 | apply canonical_nzeroP with (ltM := ltM) (p := l); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1);
 [ intros nZa1 | apply canonical_nzeroP with (ltM := ltM) (p := l0); auto ].
change
  (eqP A eqA n
     (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
              (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
              (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
              (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
              (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))
     (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
        (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
           (mults (A:=A) multA (n:=n)
              (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                 (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a0)
                 (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)
           (mults (A:=A) multA (n:=n)
              (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                 (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a1)
                 (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))))
 in |- *.
cut (canonical A0 eqA ltM l);
 [ intros Op1 | apply canonical_imp_canonical with (a := a0); auto ].
cut (canonical A0 eqA ltM l0);
 [ intros Op2 | apply canonical_imp_canonical with (a := a1); auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                  (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (T1 A1 n)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                     (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs);
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (invTerm (A:=A) invA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                     (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)));
 [ apply eqp_pluspf_com with (1 := cs); auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (invTerm (A:=A) invA (n:=n)
                  (multTerm (A:=A) multA (n:=n) (T1 A1 n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                     (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)));
 [ apply eqp_pluspf_com with (1 := cs); auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                     (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)));
 [ apply eqp_pluspf_com with (1 := cs); auto;
    apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto
 | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                        (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)));
 [ apply eqp_pluspf_com with (1 := cs); auto | idtac ].
apply canonical_mults with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                        (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_dist_pluspf with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a0)
                     (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a1 a0) (b:=a1)
                        (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a0)
                  (canonical_nzeroP A A0 eqA n ltM a0 l Cpxa1)) l)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a0 a1) (b:=a1)
                     (canonical_nzeroP A A0 eqA n ltM a1 l0 Cpxa0)) l0)));
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem spolyf_def :
 forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n))
   (Cpxa : canonical A0 eqA ltM (pX a p))
   (Cpxb : canonical A0 eqA ltM (pX b q)),
 eqP A eqA n (spolyf (pX a p) (pX b q) Cpxa Cpxb)
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)).
intros a b nZa nZb p q Cpxa Cpxb; simpl in |- *; auto.
cut (canonical A0 eqA ltM p); [ intros Op1 | auto ]; auto.
cut (canonical A0 eqA ltM q); [ intros Op2 | auto ]; unfold LetP in |- *;
 simpl in |- *; auto.
apply canonical_imp_canonical with (a := b); auto.
apply canonical_imp_canonical with (a := a); auto.
Qed.
Hint Resolve spolyf_def.
 
Theorem eqTerm_spolyf_red2 :
 forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)),
 divP A A0 eqA multA divA n c a ->
 divP A A0 eqA multA divA n c b ->
 forall (p q r : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p))
   (Cpxb : canonical A0 eqA ltM (pX b q)),
 canonical A0 eqA ltM r ->
 eqP A eqA n
   (mults (A:=A) multA (n:=n)
      (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
         (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
      (spolyf (pX a p) (pX b q) Cpxa Cpxb))
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c b
         nZb r q)
      (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec c a
         nZa r p)).
intros a b c nZa nZb nZppab H' H'0 p q r Cpxa Cpxb H'4.
cut (canonical A0 eqA ltM p);
 [ intros Op | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q);
 [ intros Oq | apply canonical_imp_canonical with (a := b); auto ].
cut (divP A A0 eqA multA divA n (ppc (A:=A) A1 (n:=n) a b) a);
 [ intros div1 | apply divP_ppcl with (1 := cs); auto ].
cut (divP A A0 eqA multA divA n (ppc (A:=A) A1 (n:=n) a b) b);
 [ intros div2 | apply divP_ppcr with (1 := cs); auto ].
cut (divP A A0 eqA multA divA n c (ppc (A:=A) A1 (n:=n) a b));
 [ intros div3 | elim ppc_is_ppcm with (1 := cs); auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
               (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)))).
apply mults_comp with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)); 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) c);
 [ intros Z2 | inversion_clear H'0; auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                  (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                  (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))));
 [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa)) p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa)
               p)
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)));
 [ auto | idtac ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_compo with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa)
               p)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa)
               p)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (multTerm (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                        (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                        (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb)) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply eqp_pluspf_com with (1 := cs);
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa)
               p)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_compo with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa)
               p)); [ auto | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pO A n)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
                  r)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply minuspf_refl with (1 := cs);
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec r
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec r
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                        nZa) p)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                        nZb) q)) r)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                        nZb) q)))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))).
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n) (T1 A1 n)
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                        nZa) p)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n)))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                        nZa) p)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n)
                     (multTerm (A:=A) multA (n:=n) 
                        (T1 A1 n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                        nZa) p)))); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (multTerm (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n)))
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                        nZa) p)))).
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) r)
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                     (mults (A:=A) multA (n:=n)
                        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                           (b:=a) nZa) p))))).
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec r
                  (mults (A:=A) multA (n:=n)
                     (invTerm (A:=A) invA (n:=n) (T1 A1 n))
                     (mults (A:=A) multA (n:=n)
                        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                           (b:=a) nZa) p))))).
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
                  (mults (A:=A) multA (n:=n)
                     (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                        nZa) p)))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply canonical_mults with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b)
                     nZb) q))
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec r
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a)
                     nZa) p))); auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 auto.
Qed.
 
Theorem eqTerm_spolyf_red3 :
 forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n))
   (Cpxa : canonical A0 eqA ltM (pX a p))
   (Cpxb : canonical A0 eqA ltM (pX b q)),
 canonical A0 eqA ltM r ->
 eqP A eqA n (spolyf (pX a p) (pX b q) Cpxa Cpxb)
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
         (ppc (A:=A) A1 (n:=n) a b) b nZb r q)
      (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
         (ppc (A:=A) A1 (n:=n) a b) a nZa r p)).
intros a b nZa nZb p q r Cpxa Cpxb H'1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b));
 [ intros nZppab | auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) (T1 A1 n)
            (spolyf (pX a p) (pX b q) Cpxa Cpxb)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
               (ppc (A:=A) A1 (n:=n) a b) (b:=ppc (A:=A) A1 (n:=n) a b)
               nZppab) (spolyf (pX a p) (pX b q) Cpxa Cpxb)).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqTerm_spolyf_red2; auto.
Qed.
 
Theorem spoly_is_minus :
 forall (a b : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n))
   (Cpxa : canonical A0 eqA ltM (pX a p))
   (Cpxb : canonical A0 eqA ltM (pX b q)),
 eqP A eqA n (spolyf (pX a p) (pX b q) Cpxa Cpxb)
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) 
         (pX a p))
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
            (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) 
         (pX b q))).
simpl in |- *; unfold LetP in |- *; simpl in |- *.
intros a b nZa nZb p q Cpxa Cpxb.
cut (canonical A0 eqA ltM p);
 [ intros Op | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM q);
 [ intros Oq | apply canonical_imp_canonical with (a := b); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b));
 [ intros nZppab | auto ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
       (mults (A:=A) multA (n:=n)
          (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
             (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p)
       (mults (A:=A) multA (n:=n)
          (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
             (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q)); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (pX (ppc (A:=A) A1 (n:=n) a b)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) p))
            (pX (ppc (A:=A) A1 (n:=n) a b)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) q))).
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply minuspf_zero with (1 := cs); auto.
cut
 (eqTerm (A:=A) eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)
    (multTerm (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
          (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) a)); 
 [ intros Z2 | auto ].
cut
 (eqTerm (A:=A) eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)
    (multTerm (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
          (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) b)); 
 [ intros Z3 | auto ].
apply minuspf_comp with (1 := cs); auto.
apply
 canonical_pX_eqT
  with
    (a := multTerm (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
               (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) a); 
 auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
           (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p))) 
 in |- *; auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
apply
 canonical_pX_eqT
  with
    (a := multTerm (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
               (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) b); 
 auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
           (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) (pX b q))) 
 in |- *; auto.
apply (eqT_sym A n); apply (eqTerm_imp_eqT A eqA n); auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
           (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) (pX a p))) 
 in |- *; auto.
change
  (canonical A0 eqA ltM
     (mults (A:=A) multA (n:=n)
        (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
           (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) (pX b q))) 
 in |- *; auto.
Qed.
 
Theorem spoly_div_is_minus :
 forall (a b c : Term A n) (nZa : ~ zeroP (A:=A) A0 eqA (n:=n) a)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (nZppab : ~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) a b)),
 divP A A0 eqA multA divA n c a ->
 divP A A0 eqA multA divA n c b ->
 forall (p q : list (Term A n)) (Cpxa : canonical A0 eqA ltM (pX a p))
   (Cpxb : canonical A0 eqA ltM (pX b q)),
 eqP A eqA n
   (mults (A:=A) multA (n:=n)
      (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
         (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
      (spolyf (pX a p) (pX b q) Cpxa Cpxb))
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=a) nZa)
         (pX a p))
      (mults (A:=A) multA (n:=n)
         (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c (b:=b) nZb)
         (pX b q))).
intros a b c nZa nZb nZppab H' H'0 p q Cpxa Cpxb.
cut (canonical A0 eqA ltM p);
 [ intros Op | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM q);
 [ intros Oq | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros Z2 | idtac ].
cut (divP A A0 eqA multA divA n c (ppc (A:=A) A1 (n:=n) a b));
 [ intros div1 | idtac ].
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
               (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) 
                  (pX a p))
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) 
                  (pX b q)))).
apply mults_comp with (1 := cs); auto.
apply spoly_is_minus; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                  (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa) 
                  (pX a p)))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                  (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
               (mults (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb) 
                  (pX b q)))).
apply mults_dist_minuspf with (1 := cs); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=a) nZa)) 
               (pX a p))
            (mults (A:=A) multA (n:=n)
               (multTerm (A:=A) multA (n:=n)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) c
                     (b:=ppc (A:=A) A1 (n:=n) a b) nZppab)
                  (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                     (ppc (A:=A) A1 (n:=n) a b) (b:=b) nZb)) 
               (pX b q))).
apply minuspf_comp with (1 := cs); auto;
 apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply minuspf_comp with (1 := cs); auto.
apply mults_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_compo with (1 := cs);
 auto.
apply mults_comp with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_compo with (1 := cs);
 auto.
case ppc_is_ppcm with (1 := cs) (a := a) (b := b); auto.
apply (divP_inv1 _ A0 eqA multA divA n) with (b := a); auto.
Qed.
 
Inductive ReduStarConfluent (Q : list (poly A0 eqA ltM))
(p : list (Term A n)) : Prop :=
    ReduStarConfluent0 :
      (forall r s : list (Term A n),
       reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
         p r ->
       reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
         p s -> eqP A eqA n r s) -> ReduStarConfluent Q p.
 
Theorem confl_under :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 (forall q : list (Term A n),
  canonical A0 eqA ltM q ->
  ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) ->
 forall r s : list (Term A n),
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p) (pX a r) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p) (pX a s) ->
 forall r1 s1 : list (Term A n),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (pX a r) r1 ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (pX a s) s1 -> eqP A eqA n r1 s1.
intros Q a p Op1 H'0 r s H'1 H'2 r1 s1 H'3 H'4.
cut (canonical A0 eqA ltM p);
 [ intros Op2 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM (pX a r));
 [ intros Op3 | apply canonical_reduce with (1 := cs) (3 := H'1); auto ].
cut (canonical A0 eqA ltM r);
 [ intros Op4 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM (pX a s));
 [ intros Op5 | apply canonical_reduce with (1 := cs) (3 := H'2); auto ].
cut (canonical A0 eqA ltM s);
 [ intros Op6 | apply canonical_imp_canonical with (a := a); auto ].
lapply (H'0 p);
 [ intros H'5; lapply H'5;
    [ intros H'6; elim H'6; clear H'5 | apply ltP_refl_pX with (1 := cs) ]
 | idtac ]; auto.
intros H'5.
elim
 reduce0_reducestar
  with (1 := cs) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := s);
 auto; intros s0 E.
elim
 reduce0_reducestar
  with (1 := cs) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (Q := Q) (p := r);
 auto; intros r0 E0.
cut
 (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (pX a r) (pX a r0));
 [ intros red1 | apply reduceplus_skip with (1 := cs); auto; elim E0 ]; 
 auto.
cut (canonical A0 eqA ltM (pX a r0));
 [ intros Op7 | apply canonical_reduceplus with (1 := cs) (3 := red1) ]; 
 auto.
cut
 (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (pX a s) (pX a s0));
 [ intros red2 | apply reduceplus_skip with (1 := cs); auto; elim E ]; 
 auto.
cut (canonical A0 eqA ltM (pX a s0));
 [ intros Op8 | apply canonical_reduceplus with (1 := cs) (3 := red2) ]; 
 auto.
cut (eqP A eqA n (pX a r0) (pX a s0)); [ intros eqPR1 | auto ].
elim
 reduce0_reducestar
  with
    (1 := cs)
    (eqA_dec := eqA_dec)
    (ltM_dec := ltM_dec)
    (Q := Q)
    (p := pX a r0); auto; intros t0 E1.
elim
 reduce0_reducestar
  with
    (1 := cs)
    (eqA_dec := eqA_dec)
    (ltM_dec := ltM_dec)
    (Q := Q)
    (p := pX a s0); auto; intros t1 E2.
cut
 (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (pX a r) t0);
 [ intros red3
 | apply
    (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n
       ltM ltM_dec os Q) with (y := pX a r0) ]; auto.
cut
 (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (pX a s) t1);
 [ intros red4
 | apply
    (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n
       ltM ltM_dec os Q) with (y := pX a s0) ]; auto.
cut (eqP A eqA n t0 t1); [ intros eqPR2 | auto ].
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t0); auto.
lapply (H'0 (pX a r));
 [ intros H'7; lapply H'7; [ intros H'8; elim H'8; clear H'7 | clear H'7 ]
 | idtac ]; auto.
apply ltP_reduce with (1 := cs) (3 := H'1); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t1); auto.
lapply (H'0 (pX a s));
 [ intros H'7; lapply H'7; [ intros H'8; elim H'8; clear H'7 | clear H'7 ]
 | idtac ]; auto.
apply ltP_reduce with (1 := cs) (3 := H'2); auto.
lapply
 (reducestar_eqp_com _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os Q
    (pX a r0) t0 (pX a s0) t0);
 [ intros H'11; lapply H'11;
    [ intros H'12; lapply H'12;
       [ intros H'13; lapply H'13;
          [ intros H'14; clear H'13 H'12 H'11 | clear H'13 H'12 H'11 ]
       | clear H'12 H'11 ]
    | clear H'11 ]
 | idtac ]; auto.
lapply (H'0 (pX a s0));
 [ intros H'7; lapply H'7; [ intros H'8; elim H'8; clear H'7 | clear H'7 ]
 | idtac ]; auto.
elim
 order_reduceplus
  with
    (1 := cs)
    (Q := Q)
    (p := pX a s)
    (q := pX a s0)
    (ltM_dec := ltM_dec)
    (eqA_dec := eqA_dec); auto.
intros H'13; apply ltP_trans with (y := pX a s); auto.
apply
 ltP_reduce with (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec) (Q := Q);
 auto.
intros H'13;
 apply (ltp_eqp_comp A A0 eqA) with (ltM := ltM) (p := pX a s) (q := pX a p);
 auto.
apply
 ltP_reduce with (Q := Q) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec);
 auto.
apply eqpP1; auto.
apply H'5; auto.
inversion_clear E0; auto.
apply reducestar0; auto.
apply Rstar_n with (y := r); auto.
apply reduce_inv with (1 := cs) (3 := H'1); auto.
apply reducestar0; auto.
apply Rstar_n with (y := s); auto.
apply reduce_inv with (1 := cs) (3 := H'2); auto.
inversion_clear E; auto.
inversion_clear E; auto.
Qed.
 
Inductive Spoly_1 (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> list (Term A n) -> Prop :=
  | Spoly_10 :
      forall (p q : list (Term A n)) (Cp : canonical A0 eqA ltM p)
        (Cq : canonical A0 eqA ltM q),
      reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
        (spolyf p q Cp Cq) (pO A n) -> Spoly_1 Q p q
  | Spoly_11 :
      forall (b c d : Term A n) (q r r0 s0 t : list (Term A n)),
      Spoly_1 Q (pX c r) (pX d t) ->
      Spoly_1 Q (pX d t) (pX b q) ->
      inPolySet A A0 eqA n ltM (pX d t) Q ->
      divP A A0 eqA multA divA n (ppc (A:=A) A1 (n:=n) c b) d ->
      Spoly_1 Q (pX c r) (pX b q).
 
Inductive SpolyQ (Q : list (poly A0 eqA ltM)) : Prop :=
    SpolyQ0 :
      (forall p q : list (Term A n),
       inPolySet A A0 eqA n ltM p Q ->
       canonical A0 eqA ltM p ->
       inPolySet A A0 eqA n ltM q Q ->
       canonical A0 eqA ltM q -> Spoly_1 Q p q) -> 
      SpolyQ Q.
 
Inductive Reducep (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop :=
    Reducep0 :
      forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
        (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)),
      reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
        (pX a p)
        (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
           b nZb p q) ->
      reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
        (pX a p)
        (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
           c nZc p r) ->
      divP A A0 eqA multA divA n a b ->
      inPolySet A A0 eqA n ltM (pX b q) Q ->
      divP A A0 eqA multA divA n a c ->
      inPolySet A A0 eqA n ltM (pX c r) Q ->
      Reducep Q (pX a p) (pX b q) (pX c r).
 
Inductive Confluent (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> list (Term A n) -> list (Term A n) -> Prop :=
    Confluent0 :
      forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
        (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)),
      (forall r1 s1 : list (Term A n),
       reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
         (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            b nZb p q) r1 ->
       reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
         (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            c nZc p r) s1 -> eqP A eqA n r1 s1) ->
      Confluent Q (pX a p) (pX b q) (pX c r).
 
Theorem Conf_inv1 :
 forall (Q : list (poly A0 eqA ltM)) (a b c : Term A n)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r r1 s1 : list (Term A n)),
 Confluent Q (pX a p) (pX b q) (pX c r) ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p q) r1 ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc
      p r) s1 -> eqP A eqA n r1 s1.
intros Q a b c nZb nZc p q r r1 s1 H'0 H'1 H'2; inversion_clear H'0.
apply H.
rewrite sp_rew with (1 := cs) (a := a) (b := b) (nZ2 := nZb); auto.
rewrite sp_rew with (1 := cs) (a := a) (b := c) (nZ2 := nZc); auto.
Qed.
 
Theorem Conf_trans :
 forall (Q : list (poly A0 eqA ltM)) (a b c d : Term A n)
   (p0 q r t : list (Term A n)),
 Reducep Q (pX a p0) (pX c r) (pX d t) ->
 Reducep Q (pX a p0) (pX d t) (pX b q) ->
 Confluent Q (pX a p0) (pX c r) (pX d t) ->
 Confluent Q (pX a p0) (pX d t) (pX b q) ->
 canonical A0 eqA ltM (pX a p0) ->
 canonical A0 eqA ltM (pX d t) -> Confluent Q (pX a p0) (pX c r) (pX b q).
intros Q a b c d p q r t H' H'0 H'1 H'2 H'3 H'4.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros nZb | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) c); [ intros nZc | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) d); [ intros nZd | idtac ].
apply Confluent0 with (nZb := nZc) (nZc := nZb); auto.
intros r1 s1 H'5 H'6.
elim
 reduce0_reducestar
  with
    (eqA_dec := eqA_dec)
    (ltM_dec := ltM_dec)
    (1 := cs)
    (Q := Q)
    (p := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            d nZd p t); auto.
intros t0 E; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t0).
apply
 Conf_inv1
  with
    (Q := Q)
    (a := a)
    (b := c)
    (c := d)
    (nZb := nZc)
    (nZc := nZd)
    (p := p)
    (q := r)
    (r := t); auto.
apply
 Conf_inv1
  with
    (Q := Q)
    (a := a)
    (b := d)
    (c := b)
    (nZb := nZd)
    (nZc := nZb)
    (p := p)
    (q := t)
    (r := q); auto.
apply canonical_spminusf with (1 := cs); auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := d); auto.
inversion_clear H'; auto.
apply canonical_nzeroP with (ltM := ltM) (p := t); auto.
apply canonical_nzeroP with (ltM := ltM) (p := r); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
inversion_clear H'; auto.
apply canonical_nzeroP with (ltM := ltM) (p := q); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
inversion_clear H'0; auto.
Qed.
 
Theorem confl_top_simpl :
 forall (Q : list (poly A0 eqA ltM)) (a b c : Term A n)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n))
   (Cpxc : canonical A0 eqA ltM (pX c r))
   (Cpxb : canonical A0 eqA ltM (pX b q)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spolyf (pX c r) (pX b q) Cpxc Cpxb) (pO A n) ->
 canonical A0 eqA ltM (pX a p) ->
 divP A A0 eqA multA divA n a b ->
 inPolySet A A0 eqA n ltM (pX b q) Q ->
 divP A A0 eqA multA divA n a c ->
 inPolySet A A0 eqA n ltM (pX c r) Q ->
 (forall q : list (Term A n),
  canonical A0 eqA ltM q ->
  ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p)
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p q) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p)
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc
      p r) ->
 forall r1 s1 : list (Term A n),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p q) r1 ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc
      p r) s1 -> eqP A eqA n r1 s1.
intros Q a b c nZb nZc p q r Cpxc Cpxb red_r0 Cpxa divP_ab in_bp_Q divP_ac
 in_cr_Q Rec red1 red2 r1 s1 reds1 reds2.
cut (canonical A0 eqA ltM p);
 [ intros Op1 | apply canonical_imp_canonical with a; auto ].
cut (canonical A0 eqA ltM r);
 [ intros Op2 | apply canonical_imp_canonical with c; auto ].
cut (canonical A0 eqA ltM q);
 [ intros Op3 | apply canonical_imp_canonical with b; auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros nZa | idtac ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) (ppc (A:=A) A1 (n:=n) c b));
 [ intros nZppcd | idtac ].
cut
 (eqP A eqA n
    (mults (A:=A) multA (n:=n)
       (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a
          (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd)
       (spolyf (pX c r) (pX b q) Cpxc Cpxb))
    (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
       (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b
          nZb p q)
       (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c
          nZc p r))); [ intros red3 | apply eqTerm_spolyf_red2; auto ].
2: apply ppc_nZ with (1 := cs); auto.
2: apply canonical_nzeroP with (ltM := ltM) (p := p); auto.
inversion_clear red_r0.
lapply
 (reduceplus_mults _ _ _ _ _ _ _ _ _ cs eqA_dec n ltM ltM_dec os Q
    (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a
       (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd)
    (spolyf (pX c r) (pX b q) Cpxc Cpxb) (pO A n));
 [ intros H'3; lapply H'3;
    [ intros H'4; lapply H'4; [ intros H'5; clear H'4 H'3 | clear H'4 H'3 ]
    | clear H'3 ]
 | idtac ]; auto.
elim
 (red_minus_zero_reduce _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ ltM_dec os Q
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b
       nZb p q)
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c
       nZc p r));
 [ intros r2 E; elim E; intros H'6 H'7; clear E | idtac | idtac | idtac ];
 auto.
2: apply canonical_spminusf with (1 := cs); auto.
2: apply canonical_spminusf with (1 := cs); auto.
elim
 reduce0_reducestar
  with (1 := cs) (Q := Q) (p := r2) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec);
 auto.
intros t0 E;
 lapply
  (Rec
     (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b
        nZb p q));
 [ intros H'1; lapply H'1; [ intros H'2; elim H'2; clear H'1 | clear H'1 ]
 | idtac ]; auto.
intros H'.
lapply
 (Rec
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c
       nZc p r));
 [ intros H'1; lapply H'1; [ intros H'3; elim H'3; clear H'1 | clear H'1 ]
 | idtac ]; auto.
intros H'1.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t0).
apply H'; auto.
auto;
 apply
  (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
     ltM_dec os Q) with (y := r2); auto.
apply canonical_spminusf with (1 := cs); auto.
apply H'1; auto.
apply
 (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
    ltM_dec os Q) with (y := r2); auto.
apply canonical_spminusf with (1 := cs); auto.
apply
 ltP_reduce with (Q := Q) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec);
 auto.
apply canonical_spminusf with (1 := cs); auto.
apply
 ltP_reduce with (Q := Q) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec);
 auto.
apply canonical_spminusf with (1 := cs); auto.
apply canonical_reduceplus with (1 := cs) (3 := H'7); auto.
apply canonical_spminusf with (1 := cs); auto.
apply
 reduceplus_eqp_com
  with
    (p := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a
               (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd)
            (spolyf (pX c r) (pX b q) Cpxc Cpxb))
    (q := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a
               (b:=ppc (A:=A) A1 (n:=n) c b) nZppcd) 
            (pO A n))
    (1 := cs); auto; simpl in |- *; auto.
Qed.
 
Theorem fconfl_top :
 forall (Q : list (poly A0 eqA ltM)) (q r : list (Term A n)),
 Spoly_1 Q q r ->
 forall p : list (Term A n),
 Reducep Q p q r ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 (forall q0 : list (Term A n),
  canonical A0 eqA ltM q0 ->
  ltP (A:=A) (n:=n) ltM q0 p -> ReduStarConfluent Q q0) -> 
 Confluent Q p q r.
intros Q q r Spoly1; elim Spoly1; clear Spoly1 q r.
intros q r Cq Cr red0 p H'1;
 (generalize Cq Cr red0; inversion_clear H'1; clear red0 Cq Cr).
intros Cq Cr H' H'0 H'1 H'2 H'3.
apply Confluent0 with (nZb := nZb) (nZc := nZc); auto.
intros r1 s1 H'5 H'6.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply (confl_top_simpl Q a c b nZc nZb p0 r0 q0 Cq Cr); auto.
intros b c d q r H' H'0 t H'1 H'2 H'3 H'4 H'5 H'6 p H'7 H'8 H'9 H'10 H'11.
generalize H'11 H'8; clear H'11 H'8; inversion_clear H'7.
intros H'8 H'11.
cut (divP A A0 eqA multA divA n a d); [ intros div0 | idtac ].
2: apply
    (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := ppc (A:=A) A1 (n:=n) c b);
    auto.
2: case ppc_is_ppcm with (1 := cs) (a := c) (b := b); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) d); [ intros nZd | inversion div0 ]; auto.
cut (Reducep Q (pX a p0) (pX d t) (pX b q)); [ intros Red0 | idtac ].
2: apply Reducep0 with (nZb := nZd) (nZc := nZc); auto.
cut (Reducep Q (pX a p0) (pX c r) (pX d t)); [ intros Red1 | idtac ].
2: apply Reducep0 with (nZb := nZb) (nZc := nZd); auto.
apply Conf_trans with (d := d) (t := t); auto.
apply H'2; auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply H'4; auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
apply reducetop_sp with (1 := cs); auto.
apply reducetop_sp with (1 := cs); auto.
Qed.
 
Theorem confl_top :
 forall Q : list (poly A0 eqA ltM),
 SpolyQ Q ->
 forall (a b c : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b)
   (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q r : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 divP A A0 eqA multA divA n a b ->
 inPolySet A A0 eqA n ltM (pX b q) Q ->
 divP A A0 eqA multA divA n a c ->
 inPolySet A A0 eqA n ltM (pX c r) Q ->
 (forall q : list (Term A n),
  canonical A0 eqA ltM q ->
  ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p)
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p q) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p)
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc
      p r) ->
 forall r1 s1 : list (Term A n),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p q) r1 ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a c nZc
      p r) s1 -> eqP A eqA n r1 s1.
intros Q H' a b c nZb nZc p q r H'0 H'1 H'2 H'3 H'4 H'5 H'6 H'7 r1 s1 H'8 H'9.
cut (canonical A0 eqA ltM (pX b q)); [ intros Op0 | idtac ].
cut (canonical A0 eqA ltM (pX c r)); [ intros Op0bis | idtac ].
cut (Confluent Q (pX a p) (pX b q) (pX c r)); auto.
2: apply fconfl_top; auto.
2: inversion_clear H'; auto.
2: apply Reducep0 with (nZb := nZb) (nZc := nZc); auto.
2: apply inPolySet_imp_canonical with (L := Q); auto.
2: apply inPolySet_imp_canonical with (L := Q); auto.
intros H'10.
apply (Conf_inv1 Q a b c nZb nZc p q r r1 s1); auto.
Qed.
 
Theorem confl_mix :
 forall (Q : list (poly A0 eqA ltM)) (a b : Term A n)
   (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q r : list (Term A n)),
 canonical A0 eqA ltM (pX a p) ->
 divP A A0 eqA multA divA n a b ->
 inPolySet A A0 eqA n ltM (pX b r) Q ->
 (forall q : list (Term A n),
  canonical A0 eqA ltM q ->
  ltP (A:=A) (n:=n) ltM q (pX a p) -> ReduStarConfluent Q q) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p) (pX a q) ->
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
   (pX a p)
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p r) ->
 forall r1 s1 : list (Term A n),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (pX a q) r1 ->
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b nZb
      p r) s1 -> eqP A eqA n r1 s1.
intros Q a b nZb p q r Op1 dviP_ab in_br Rec red1 red2 r1 s1 red3 red4.
cut (canonical A0 eqA ltM (pX b r));
 [ intros Op2 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q);
 [ intros H'6 | apply reduce_inv with (1 := cs) (3 := red1); auto ].
cut (canonical A0 eqA ltM p);
 [ intros Op3 | apply canonical_imp_canonical with (a := a); auto ].
cut (canonical A0 eqA ltM r);
 [ intros Op4 | apply canonical_imp_canonical with (a := b); auto ].
cut (canonical A0 eqA ltM q);
 [ intros Op5 | apply canonical_reduce with (1 := cs) (3 := H'6); auto ].
case
 one_minus_reduceplus
  with
    (plusA := plusA)
    (3 := H'6)
    (r := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) r);
 auto.
intros s H; elim H; intros H0 H1; clear H.
cut (canonical A0 eqA ltM s);
 [ intros Op6 | apply canonical_reduceplus with (1 := cs) (3 := H1); auto ].
elim
 reduce0_reducestar
  with (Q := Q) (p := s) (1 := cs) (ltM_dec := ltM_dec) (eqA_dec := eqA_dec);
 auto; intros t E.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := t); auto.
lapply (Rec (pX a q));
 [ intros H'0; lapply H'0; [ intros H'1; elim H'1; clear H'0 | clear H'0 ]
 | idtac ]; auto.
intros PH'0; apply PH'0; auto.
apply
 (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
    ltM_dec os Q) with (y := s); auto.
apply canonical_reduce with (1 := cs) (3 := red1); auto.
apply
 Rstar_n
  with
    (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec q
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb)
               r)); auto.
apply reducetop with (b := b) (nZb := nZb) (q := r); auto.
apply ltP_reduce with (1 := cs) (3 := red1); auto.
apply canonical_reduce with (1 := cs) (3 := red1); auto.
lapply
 (Rec
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a b
       nZb p r));
 [ intros H'0; lapply H'0; [ intros H'1; elim H'1; clear H'0 | clear H'0 ]
 | idtac ]; auto.
intros PH'0; apply PH'0; auto.
apply
 (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
    ltM_dec os Q) with (y := s); auto.
apply canonical_spminusf with (1 := cs); auto.
apply ltP_reduce with (1 := cs) (3 := red2); auto.
apply canonical_spminusf with (1 := cs); auto.
Qed.
Hint Resolve pO_irreducible.
 
Theorem confl_restar :
 forall Q : list (poly A0 eqA ltM),
 SpolyQ Q ->
 forall p : poly A0 eqA ltM, ReduStarConfluent Q (s2p A A0 eqA n ltM p).
intros Q H'.
intros p; pattern p in |- *;
 apply
  well_founded_ind
   with (R := sltP (A:=A) (A0:=A0) (eqA:=eqA) (n:=n) (ltM:=ltM)); 
 auto.
apply sltp_wf; auto.
intros x; elim x; clear x.
intros x Op_x Rec; simpl in |- *.
apply ReduStarConfluent0; auto.
intros r s H'1 H'2.
case reducestar_inv with (1 := cs) (3 := H'2); auto; intros H'8; elim H'8;
 clear H'8.
case reducestar_inv with (1 := cs) (3 := H'1); auto; intros H'9; elim H'9;
 clear H'9.
intros H H0 H1 H2; apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := x);
 auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x0 H H0 H1; elim H; intros H2 H3;
 absurd
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x x0);
 auto.
intros x0 H; elim H; intros H0 H1; clear H.
case reducestar_inv with (1 := cs) (3 := H'1); auto; intros H'9; elim H'9;
 clear H'9.
intros H H2;
 absurd
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x x0);
 auto.
intros x1 H; elim H; intros H2 H3; clear H.
generalize H3 H0 H'1 Op_x Rec; clear H3 H0 H'1 Rec Op_x; inversion H2.
intros H'3 H'4 H'5 Op_x H'6.
generalize Op_x H'6 H'5 H'3; clear H'5 H'3 H'6 Op_x.
inversion H'4.
intros Op_x H'6 H'5 H'3.
apply
 confl_top
  with
    (Q := Q)
    (a := a)
    (b := b)
    (c := b0)
    (nZb := nZb)
    (nZc := nZb0)
    (p := p0)
    (q := q)
    (r := q0); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducetop_sp with (1 := cs); auto.
apply reducetop_sp with (1 := cs); auto.
apply reducestar_eqp_com with (1 := cs) (p := x1) (q := r); auto.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H4; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (1 := cs) (p := x0) (q := s); auto.
apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros Op_x H'6 H'5 H'3.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
apply
 confl_mix
  with (Q := Q) (a := a) (b := b) (nZb := nZb) (p := p0) (q := q0) (r := q);
 auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducetop_sp with (1 := cs); auto.
apply reducestar_eqp_com with (p := pX b0 q0) (q := s) (1 := cs); auto.
rewrite H9; auto.
rewrite H9.
apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (1 := cs) (p := x1) (q := r); auto.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H4; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros H'3 H'4 H'5 Op_x H'6.
inversion H'4.
apply (confl_mix Q a b0 nZb p0 q q0); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducetop_sp with (1 := cs); auto.
apply reducestar_eqp_com with (1 := cs) (p := pX b q) (q := r); auto.
rewrite H4; auto.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H3; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (1 := cs) (p := x0) (q := s); auto.
apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply confl_under with (Q := Q) (a := a) (p := p0) (r := q) (s := q0); auto.
intros q1 H'9 H'10.
generalize (H'6 (mks A A0 eqA n ltM q1 H'9)); simpl in |- *; auto.
apply reducestar_eqp_com with (1 := cs) (p := pX b q) (q := r); auto.
rewrite H4.
apply canonical_reduce with (1 := cs) (3 := H2); auto.
rewrite <- H3; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply reducestar_eqp_com with (p := pX b0 q0) (q := s) (1 := cs); auto.
rewrite H8; auto.
rewrite H8; apply canonical_reduce with (1 := cs) (3 := H'4); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem confl_reducestar :
 forall Q : list (poly A0 eqA ltM),
 SpolyQ Q ->
 forall p : list (Term A n), canonical A0 eqA ltM p -> ReduStarConfluent Q p.
intros Q H' p H'0.
generalize (confl_restar Q H' (mks A A0 eqA n ltM p H'0)); simpl in |- *;
 auto.
Qed.
End Pspoly.