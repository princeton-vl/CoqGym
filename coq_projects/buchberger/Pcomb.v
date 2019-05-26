(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export Pspoly.
Require Export LetP.

Local Unset Injection On Proofs.

Section Pcomb.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hSpoly".
 
Inductive CombLinear (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> Prop :=
  | CombLinear_0 : CombLinear Q (pO A n)
  | CombLinear_1 :
      forall (a : Term A n) (p q s : list (Term A n)),
      ~ zeroP (A:=A) A0 eqA (n:=n) a ->
      inPolySet A A0 eqA n ltM q Q ->
      CombLinear Q p ->
      eqP A eqA n s
        (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
           (mults (A:=A) multA (n:=n) a q) p) -> CombLinear Q s.
Hint Resolve CombLinear_0 CombLinear_1.
 
Theorem CombLinear_canonical :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 CombLinear Q p -> canonical A0 eqA ltM p.
intros Q p H'; elim H'; auto.
intros a p0 q s H'0 H'1 H'2 H'3 H'4.
apply
 eqp_imp_canonical
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) p0)
    (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
Qed.
 
Theorem CombLinear_comp :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 CombLinear Q p ->
 forall q : list (Term A n),
 canonical A0 eqA ltM q -> eqP A eqA n p q -> CombLinear Q q.
intros Q p H'; elim H'; auto.
intros q H'0 H'1; inversion H'1; auto.
intros a p0 q s H'0 H'1 H'2 H'3 H'4 q0 H'5 H'6.
cut (canonical A0 eqA ltM q); [ intros C0 | idtac ].
cut (canonical A0 eqA ltM s); [ intros C1 | idtac ].
apply CombLinear_1 with (a := a) (p := p0) (q := q); auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := s); auto;
 apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_imp_canonical with (p := q0) (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
Qed.
Hint Resolve CombLinear_canonical.
 
Theorem CombLinear_pluspf :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 CombLinear Q p ->
 forall q : list (Term A n),
 CombLinear Q q ->
 CombLinear Q
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p q).
intros Q p H'; elim H'; auto.
intros q H'0.
cut (canonical A0 eqA ltM q);
 [ intros Op1 | apply CombLinear_canonical with (Q := Q); auto ].
apply CombLinear_comp with (p := q); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pO A n) q); auto; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); 
 auto.
intros a p0 q s H'0 H'1 H'2 H'3 H'4 q0 H'5.
cut (canonical A0 eqA ltM q);
 [ intros C0 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (canonical A0 eqA ltM q0);
 [ intros Op1 | apply CombLinear_canonical with (Q := Q); auto ].
cut (canonical A0 eqA ltM p0);
 [ intros Op2 | apply CombLinear_canonical with (Q := Q); auto ].
apply
 CombLinear_1
  with
    (a := a)
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p0 q0)
    (q := q); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a q) p0) q0); 
 auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply
 eqp_imp_canonical
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) p0)
    (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
Hint Resolve CombLinear_pluspf.
 
Theorem CombLinear_mults1 :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)),
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 CombLinear Q p -> CombLinear Q (mults (A:=A) multA (n:=n) a p).
intros Q a p H' H'0; elim H'0; auto.
intros a0 p0 q s H'1 H'2 H'3 H'4 H'5.
cut (canonical A0 eqA ltM q);
 [ intros C0 | apply inPolySet_imp_canonical with (L := Q); auto ].
cut (canonical A0 eqA ltM p0);
 [ intros Op1 | apply CombLinear_canonical with (Q := Q); auto ].
apply
 CombLinear_1
  with
    (a := multTerm (A:=A) multA (n:=n) a a0)
    (p := mults (A:=A) multA (n:=n) a p0)
    (q := q); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n) a
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a0 q) p0)); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) a0 q))
            (mults (A:=A) multA (n:=n) a p0)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
Hint Resolve CombLinear_mults1.
 
Theorem CombLinear_minuspf :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 CombLinear Q p ->
 forall q : list (Term A n),
 CombLinear Q q ->
 CombLinear Q
   (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p q).
intros Q p H' q H'0; try assumption.
cut (canonical A0 eqA ltM p);
 [ intros Op1 | apply CombLinear_canonical with (Q := Q); auto ].
cut (canonical A0 eqA ltM q);
 [ intros Op2 | apply CombLinear_canonical with (Q := Q); auto ].
apply
 CombLinear_comp
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            p
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               q)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
Hint Resolve CombLinear_minuspf.
 
Theorem CombLinear_id :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 inPolySet A A0 eqA n ltM p Q -> CombLinear Q p.
intros Q p H'.
cut (canonical A0 eqA ltM p);
 [ intros C0 | apply inPolySet_imp_canonical with (L := Q); auto ].
apply
 CombLinear_comp
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) (T1 A1 n) p) 
            (pO A n)); auto.
apply CombLinear_1 with (a := T1 A1 n) (p := pO A n) (q := p); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := mults (A:=A) multA (n:=n) (T1 A1 n) p); 
 auto.
Qed.
Hint Resolve CombLinear_id.
 
Theorem CombLinear_spoly :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n))
   (Cp : canonical A0 eqA ltM p) (Cq : canonical A0 eqA ltM q),
 inPolySet A A0 eqA n ltM p Q ->
 inPolySet A A0 eqA n ltM q Q ->
 CombLinear Q
   (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec p q Cp Cq).
intros Q p; case p.
simpl in |- *; auto.
intros a l q; case q.
simpl in |- *; auto.
intros a0 l0 Cp Cq H' H'0.
cut (canonical A0 eqA ltM l0);
 [ intros Op1 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
cut (canonical A0 eqA ltM l);
 [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZa | apply (canonical_nzeroP A A0 eqA n ltM) with (p := l); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros nZa0
 | apply (canonical_nzeroP A A0 eqA n ltM) with (p := l0); auto ].
apply
 CombLinear_comp
  with
    (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (ppc (A:=A) A1 (n:=n) a a0) (b:=a) nZa) 
               (pX a l))
            (mults (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
                  (ppc (A:=A) A1 (n:=n) a a0) (b:=a0) nZa0) 
               (pX a0 l0))); auto.
apply spolyf_canonical with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change
  (eqP A eqA n
     (spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
        (pX a l) (pX a0 l0) Cp Cq)
     (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
              (ppc (A:=A) A1 (n:=n) a a0) (b:=a) nZa) 
           (pX a l))
        (mults (A:=A) multA (n:=n)
           (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n)
              (ppc (A:=A) A1 (n:=n) a a0) (b:=a0) nZa0) 
           (pX a0 l0)))) in |- *.
apply spoly_is_minus with (1 := cs); auto.
Qed.
 
Theorem CombLinear_reduce :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q ->
 canonical A0 eqA ltM p -> CombLinear Q q -> CombLinear Q p.
intros Q p q H'0 H'1 H'2.
case reduce_inv2 with (1 := cs) (3 := H'0); auto.
intros x H; elim H; intros a H0; elim H0; intros H1 H2; elim H2; intros H3 H4;
 elim H4; intros H5 H6; clear H4 H2 H0 H.
apply CombLinear_1 with (a := a) (p := q) (q := x); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n).
cut (canonical A0 eqA ltM q);
 [ intros Op1 | apply canonical_reduce with (1 := cs) (3 := H'0) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a x)
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
               (mults (A:=A) multA (n:=n) a x))); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p
               (mults (A:=A) multA (n:=n) a x))
            (mults (A:=A) multA (n:=n) a x)); auto.
apply pluspf_minuspf_id with (1 := cs); auto.
Qed.
 
Theorem CombLinear_reduceplus :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q ->
 canonical A0 eqA ltM p -> CombLinear Q q -> CombLinear Q p.
intros Q p q H'0; elim H'0; auto.
intros x y H' H'1 H'2.
apply CombLinear_comp with (p := y); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H' H'1 H'2 H'3 H'4.
apply CombLinear_reduce with (q := y); auto.
apply H'2; auto.
apply canonical_reduce with (1 := cs) (3 := H'); auto.
Qed.
 
Theorem CombLinear_reducestar :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q ->
 canonical A0 eqA ltM p -> CombLinear Q q -> CombLinear Q p.
intros Q p q H'; elim H'; auto.
intros p0 q0 H'0 H'1 H'2 H'3.
apply CombLinear_reduceplus with (q := q0); auto.
Qed.
 
Theorem Reducestar_pO_imp_CombLinear :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q ->
 canonical A0 eqA ltM p -> eqP A eqA n q (pO A n) -> CombLinear Q p.
intros Q p q H' H'0 H'1; inversion H'1; auto.
apply CombLinear_reducestar with (q := q); auto.
rewrite <- H; auto.
Qed.
 
Inductive Grobner (Q : list (poly A0 eqA ltM)) : Prop :=
    Grobner0 :
      (forall p q : list (Term A n),
       CombLinear Q p ->
       reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
         p q -> eqP A eqA n q (pO A n)) -> Grobner Q.
 
Theorem Grobner_imp_SpolyQ :
 forall Q : list (poly A0 eqA ltM),
 Grobner Q ->
 SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q.
intros Q H'; elim H'.
intros H'1.
apply SpolyQ0; auto.
intros p q H'0 H'2 H'3 H'4.
elim
 reduce0_reducestar
  with
    (ltM_dec := ltM_dec)
    (eqA_dec := eqA_dec)
    (1 := cs)
    (Q := Q)
    (p := spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec p q
            H'2 H'4); auto.
intros t E; apply Spoly_10 with (Cp := H'2) (Cq := H'4); auto.
apply
 reducestar_eqp_com
  with
    (1 := cs)
    (p := spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec p q
            H'2 H'4)
    (q := t); auto.
apply spolyf_canonical with (1 := cs); auto.
apply
 H'1
  with
    (p := spolyf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec p q
            H'2 H'4); auto.
apply CombLinear_spoly; auto.
apply spolyf_canonical with (1 := cs); auto.
Qed.
 
Inductive ConfluentReduce (Q : list (poly A0 eqA ltM)) : Prop :=
    ConfluentReduce0 :
      (forall p : list (Term A n),
       canonical A0 eqA ltM p ->
       ReduStarConfluent A A0 A1 eqA invA minusA multA divA eqA_dec n ltM
         ltM_dec Q p) -> ConfluentReduce Q.
 
Theorem SpolyQ_imp_ConfluentReduce :
 forall Q : list (poly A0 eqA ltM),
 SpolyQ A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q ->
 ConfluentReduce Q.
intros Q H'0.
apply ConfluentReduce0.
intros p H'1.
change
  (ReduStarConfluent A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
     Q (s2p A A0 eqA n ltM (mks A A0 eqA n ltM p H'1))) 
 in |- *.
apply confl_restar with (1 := cs); auto.
Qed.
 
Theorem ConfluentReduce_imp_Grobner :
 forall Q : list (poly A0 eqA ltM), ConfluentReduce Q -> Grobner Q.
intros Q H'; elim H'.
intros H'0.
apply Grobner0; auto.
intros p q H'1; generalize q; clear q; elim H'1.
intros q H'2.
rewrite pO_reducestar with (1 := H'2); auto.
intros a p0 q s H'2 H'3 H'4 H'5 H'6 q0 H'7.
cut (canonical A0 eqA ltM q);
 [ intros Op0 | apply inPolySet_imp_canonical with (L := Q) ]; 
 auto.
cut (canonical A0 eqA ltM p0);
 [ intros Op2 | apply CombLinear_canonical with (Q := Q) ]; 
 auto.
cut (canonical A0 eqA ltM s); [ intros Op1 | idtac ].
cut (canonical A0 eqA ltM q0); [ intros Op2b | idtac ]; auto.
cut
 (reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (mults (A:=A) multA (n:=n) a q) (pO A n));
 [ intros H'11 | apply reducestar_in_pO with (1 := cs) ]; 
 auto.
elim
 red_minus_zero_reduce
  with
    (1 := cs)
    (Q := Q)
    (p := s)
    (q := p0)
    (ltM_dec := ltM_dec)
    (eqA_dec := eqA_dec); auto.
intros r1 H; elim H; intros H0 H1; clear H.
elim
 reduce0_reducestar
  with (ltM_dec := ltM_dec) (eqA_dec := eqA_dec) (1 := cs) (Q := Q) (p := r1);
 auto.
intros t E'.
lapply (H'0 s); [ intros H'12; inversion H'12 | idtac ]; auto.
apply H; auto.
apply reducestar_eqp_com with (1 := cs) (p := s) (q := t); auto.
apply reducestar_trans with (y := r1) (1 := cs); auto.
apply H'5; auto.
apply
 (reducestar_trans A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
    ltM_dec os Q) with (y := r1); auto.
apply canonical_reduceplus with (1 := cs) (3 := H1); auto.
apply
 reduceplus_eqp_com
  with (1 := cs) (p := mults (A:=A) multA (n:=n) a q) (q := pO A n); 
 auto.
inversion H'11; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 apply
  (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
   with
     (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec
             (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                ltM_dec (mults (A:=A) multA (n:=n) a q) p0) p0); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a q) p0)
            (mults (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) (T1 A1 n))
               p0)); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p0
               (mults (A:=A) multA (n:=n)
                  (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p0))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) (pO A n)); 
 auto.
inversion H'7.
apply canonical_reduceplus with (1 := cs) (3 := H); auto.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) p0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem CombLinear_incl :
 forall (a : list (Term A n)) (P Q : list (poly A0 eqA ltM)),
 (forall a : list (Term A n),
  inPolySet A A0 eqA n ltM a P -> inPolySet A A0 eqA n ltM a Q) ->
 CombLinear P a -> CombLinear Q a.
intros a P Q H' H'0; elim H'0; auto.
intros a0 p q s H'1 H'2 H'3 H'4 H'5.
apply
 CombLinear_comp
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a0 q) p); auto.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a0 q) p); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_pluspf with (1 := os); auto.
apply canonical_mults with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := P); auto.
apply CombLinear_canonical with (Q := Q); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Remark CombLinear_trans_cons_lem :
 forall (a : list (Term A n)) (R : list (poly A0 eqA ltM)),
 CombLinear R a ->
 forall (b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 R = b :: Q -> CombLinear Q (s2p A A0 eqA n ltM b) -> CombLinear Q a.
intros a R H'; elim H'; auto.
intros a0 p q s H'0 H'1 H'2 H'3 H'4 b Q H'5 H'6.
apply
 CombLinear_comp
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a0 q) p); auto.
2: apply
    eqp_imp_canonical
     with
       (1 := cs)
       (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a0 q) p); 
    auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
2: apply canonical_pluspf; auto.
2: apply canonical_mults with (1 := cs); auto.
2: apply inPolySet_imp_canonical with (L := R); auto.
2: apply CombLinear_canonical with (1 := H'2); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply CombLinear_pluspf; auto.
apply CombLinear_mults1; auto.
2: apply H'3 with (b := b); auto.
rewrite H'5 in H'1; inversion H'1; auto.
rewrite <- H2 in H'6; simpl in H'6; auto.
Qed.
 
Theorem reduce_cb :
 forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b ->
 canonical A0 eqA ltM a -> CombLinear Q a -> CombLinear Q b.
intros a b Q H' H'0 H'1.
cut (canonical A0 eqA ltM b);
 [ intros Op1 | apply canonical_reduce with (1 := cs) (3 := H'); auto ].
case reduce_inv2 with (1 := cs) (3 := H'); auto;
 (intros c E; elim E; intros d E0; elim E0; intros H'7 H'8; elim H'8;
   intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 H'8 E0 E); 
 auto.
apply
 CombLinear_comp
  with
    (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec a
            (mults (A:=A) multA (n:=n) d c)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem reduceplus_cb :
 forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b ->
 canonical A0 eqA ltM a -> CombLinear Q a -> CombLinear Q b.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 H'2.
apply CombLinear_comp with (p := x); auto.
apply eqp_imp_canonical with (p := x) (1 := cs); auto.
intros x y z H'0 H'1 H'2 H'3 H'4.
apply H'2; auto.
apply canonical_reduce with (1 := cs) (3 := H'0) (p := x); auto.
apply reduce_cb with (a := x); auto.
Qed.
 
Theorem reducestar_cb :
 forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b ->
 canonical A0 eqA ltM a -> CombLinear Q a -> CombLinear Q b.
intros a b Q H'; elim H'; auto.
intros p q H'0 H'1 H'2 H'3.
apply reduceplus_cb with (a := p); auto.
Qed.

Theorem reduce_cb1 :
 forall (a : poly A0 eqA ltM) (b : list (Term A n))
   (Q : list (poly A0 eqA ltM)),
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) b -> CombLinear (a :: Q) b.
intros a; case a; simpl in |- *.
intros x c b Q H'.
cut (canonical A0 eqA ltM b);
 [ intros Op1 | apply canonical_reduce with (1 := cs) (3 := H') ]; 
 auto.
case reduce_inv2 with (1 := cs) (3 := H'); auto;
 (intros c1 E; elim E; intros d E0; elim E0; intros H'7 H'8; elim H'8;
   intros H'9 H'10; elim H'10; intros H'11 H'12; clear H'10 H'8 E0 E).
apply
 CombLinear_comp
  with
    (p := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec x
            (mults (A:=A) multA (n:=n) d c1)); auto.
apply CombLinear_minuspf; auto.
apply CombLinear_id; auto.
generalize c H'; case x; auto.
intros c2 H'0; inversion H'0; auto.
intros t l c0 H'0;
 change
   (inPolySet A A0 eqA n ltM (pX t l)
      (exist (canonical A0 eqA ltM) (pX t l) c0 :: Q)) 
  in |- *; auto.
apply incons with (a := t) (p := l) (P := Q); auto.
apply CombLinear_mults1; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem CombLinear_compo :
 forall (p : list (Term A n)) (L1 : list (poly A0 eqA ltM)),
 CombLinear L1 p ->
 forall L2 : list (poly A0 eqA ltM),
 (forall q : list (Term A n),
  inPolySet A A0 eqA n ltM q L1 -> CombLinear L2 q) -> 
 CombLinear L2 p.
intros p L1 H'; elim H'; auto.
intros a p0 q s H'0 H'1 H'2 H'3 H'4 L2 H'5.
apply
 CombLinear_comp
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) p0); auto.
apply
 eqp_imp_canonical
  with
    (1 := cs)
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) p0); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply inPolySet_imp_canonical with (L := L1); auto.
apply CombLinear_canonical with (1 := H'2); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem reduceplus_cb1_lem :
 forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b ->
 forall x : poly A0 eqA ltM,
 s2p A A0 eqA n ltM x = a -> CombLinear (x :: Q) b.
intros a b Q H'; elim H'; auto.
intros x y H'0 x0; case x0; simpl in |- *; auto.
intros x1 c H'1.
apply CombLinear_comp with (p := x); auto.
rewrite <- H'1; auto.
generalize c; case x1; auto.
intros t l c0; apply CombLinear_id; auto.
change
  (inPolySet A A0 eqA n ltM (pX t l)
     (exist (canonical A0 eqA ltM) (pX t l) c0 :: Q)) 
 in |- *; auto.
apply incons with (a := t) (p := l) (P := Q); auto.
apply eqp_imp_canonical with (1 := cs) (p := x1); auto; rewrite H'1; auto.
intros x y z; case y; auto.
intros H'0 H'1 H'2 x0 H'3.
cut (canonical A0 eqA ltM (pO A n)).
intros H'4.
apply CombLinear_compo with (L1 := mks A A0 eqA n ltM (pO A n) H'4 :: Q);
 auto.
intros q H'5; inversion H'5; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply canonicalpO; auto.
intros a0 l H'0 H'1 H'2 x0 H'3.
cut (canonical A0 eqA ltM (pX a0 l)).
intros H'4.
apply CombLinear_compo with (L1 := mks A A0 eqA n ltM (pX a0 l) H'4 :: Q);
 auto.
intros q H'5; inversion H'5; auto.
apply reduce_cb1; auto.
rewrite H'3; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
generalize H'3; case x0; simpl in |- *; auto.
intros x1 H'4 H'5; elim H'5; auto.
Qed.
 
Theorem reduceplus_cb1 :
 forall (a : poly A0 eqA ltM) (b : list (Term A n))
   (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) b -> CombLinear (a :: Q) b.
intros a b Q H'.
apply reduceplus_cb1_lem with (a := s2p A A0 eqA n ltM a); auto.
Qed.
 
Theorem reducestar_cb1 :
 forall (a : poly A0 eqA ltM) (b : list (Term A n))
   (Q : list (poly A0 eqA ltM)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) b -> CombLinear (a :: Q) b.
intros a b Q H'; inversion H'; auto.
apply reduceplus_cb1; auto.
Qed.
 
Theorem reduce_cb2 :
 forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) ->
 CombLinear (b :: Q) (s2p A A0 eqA n ltM a).
intros a b; case a; case b; simpl in |- *.
intros x c x0 c1 Q H'0.
case reduce_inv2 with (1 := cs) (3 := H'0); auto; intros c0 E; elim E;
 intros d E0; elim E0; intros H'7 H'8; elim H'8; intros H'9 H'10; 
 elim H'10; intros H'11 H'12; clear H'10 H'8 E0 E.
apply
 CombLinear_comp
  with
    (p := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            x (mults (A:=A) multA (n:=n) d c0)); auto.
apply CombLinear_pluspf; auto.
generalize c H'0; case x; auto.
intros a0 l c2 H'.
apply CombLinear_id; auto.
change
  (inPolySet A A0 eqA n ltM (pX a0 l)
     (exist (canonical A0 eqA ltM) (pX a0 l) c2 :: Q)) 
 in |- *.
apply incons with (a := a0) (p := l) (P := Q); auto.
apply CombLinear_mults1; auto.
apply CombLinear_id; auto.
apply inskip; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec x0
               (mults (A:=A) multA (n:=n) d c0))
            (mults (A:=A) multA (n:=n) d c0)); auto.
apply pluspf_minuspf_id with (1 := cs); auto.
Qed.
 
Theorem reduceplus_cb2_lem :
 forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b ->
 canonical A0 eqA ltM a ->
 forall x : poly A0 eqA ltM,
 s2p A A0 eqA n ltM x = b -> CombLinear (x :: Q) a.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 x0 H'2.
apply CombLinear_comp with (p := y); auto.
rewrite <- H'2; case x0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros t l c; apply CombLinear_id; auto.
change
  (inPolySet A A0 eqA n ltM (pX t l)
     (exist (fun l0 => canonical A0 eqA ltM l0) (pX t l) c :: Q)) 
 in |- *; apply incons; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros x y z H'0 H'1 H'2 H'3 x0 H'4.
lapply H'2;
 [ intros H'5; lapply (H'5 x0); [ intros H'7; clear H'2 | clear H'2 ]
 | clear H'2 ]; auto.
cut (canonical A0 eqA ltM y).
intros H'2.
lapply (reduce_cb2 (mks A A0 eqA n ltM x H'3) (mks A A0 eqA n ltM y H'2) Q);
 simpl in |- *; [ intros H'9 | idtac ]; auto.
apply
 CombLinear_trans_cons_lem
  with
    (R := mks A A0 eqA n ltM y H'2 :: x0 :: Q)
    (b := mks A A0 eqA n ltM y H'2); auto.
apply CombLinear_incl with (P := mks A A0 eqA n ltM y H'2 :: Q); auto.
intros a0 H'6.
apply Incl_inp_inPolySet with (P := mks A A0 eqA n ltM y H'2 :: Q); auto.
red in |- *; simpl in |- *; auto with datatypes.
intros a1 H'8; elim H'8; auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
apply canonical_reduce with (1 := cs) (3 := H'0); auto.
Qed.
 
Theorem reduceplus_cb2 :
 forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) ->
 CombLinear (b :: Q) (s2p A A0 eqA n ltM a).
intros a b Q H'.
apply reduceplus_cb2_lem with (b := s2p A A0 eqA n ltM b); auto.
case a; auto.
Qed.
 
Theorem reducestar_cb2 :
 forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) ->
 CombLinear (b :: Q) (s2p A A0 eqA n ltM a).
intros a b Q H'; inversion H'; auto.
apply reduceplus_cb2; auto.
Qed.
End Pcomb.