(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : multiplication over polynomials                     
                                                                           
          Laurent Thery March 98 (revised Avril 01)                          
                                                                           
  ***************************************************************************
   definition of smult*)
Require Export Pmults.
Section Pmult.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hMults".
 
Fixpoint multpf (p : list (Term A n)) : list (Term A n) -> list (Term A n) :=
  fun q : list (Term A n) =>
  match p with
  | nil => pO A n
  | a :: p' =>
      pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (mults (A:=A) multA (n:=n) a q) (multpf p' q)
  end.
 
Theorem canonical_multpf :
 forall l1 l2 : list (Term A n),
 canonical A0 eqA ltM l1 ->
 canonical A0 eqA ltM l2 -> canonical A0 eqA ltM (multpf l1 l2).
intros l1; elim l1; simpl in |- *; auto.
intros a l H' l2 H'0 H'1; try assumption.
apply canonical_pluspf; auto.
apply canonical_mults with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply H'; auto.
apply canonical_imp_canonical with (a := a); auto.
Qed.
Hint Resolve canonical_multpf.
 
Theorem pluspf_pX :
 forall (p : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM (pX a p) ->
 eqP A eqA n (pX a p)
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (pX a (pO A n)) p).
intros p; case p; clear p; auto.
intros a H;
 change
   (eqP A eqA n (pX a (pO A n))
      (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
         (pX a (pO A n)) (pO A n))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a1 p a0 H'.
cut (canonical A0 eqA ltM (pX a1 p));
 [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX a0
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pO A n) (pX a1 p))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change
  (eqP A eqA n
     (pX a0
        (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
           (pO A n) (pX a1 p)))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a0 (pO A n)) (pX a1 p))) in |- *; auto.
apply pluspf_inv1 with (1 := cs); auto.
apply (canonical_pX_order _ A0 eqA) with (l := p); auto.
Qed.
 
Theorem multpf_disr_pX :
 forall (p q : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM (pX a q) ->
 eqP A eqA n (multpf p (pX a q))
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (mults (A:=A) multA (n:=n) a p) (multpf p q)).
intros p; elim p; clear p; simpl in |- *; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros b p Rec q a Op0 Op1.
cut (canonical A0 eqA ltM q);
 [ intros Op2 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (canonical A0 eqA ltM p);
 [ intros Op3 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b);
 [ intros nZ1 | apply canonical_nzeroP with (ltM := ltM) (p := p) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) b a));
 [ intros nZ2 | idtac ]; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) a b));
 [ intros nZ3 | idtac ]; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX (multTerm (A:=A) multA (n:=n) b a)
               (mults (A:=A) multA (n:=n) b q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a p) 
               (multpf p q))); auto.
apply eqp_pluspf_com with (1 := cs); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) b (pX a q))) in |- *;
 auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) b (pX a q))) in |- *;
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n))
               (mults (A:=A) multA (n:=n) b q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a p) 
               (multpf p q))); auto.
cut
 (canonical A0 eqA ltM
    (pX (multTerm (A:=A) multA (n:=n) b a) (mults (A:=A) multA (n:=n) b q)));
 [ intros Op4 | idtac ]; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply pluspf_pX; auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) b (pX a q))) in |- *;
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b q)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) a p) 
                  (multpf p q)))); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b q)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (multpf p q) (mults (A:=A) multA (n:=n) a p))));
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) b q) 
                  (multpf p q)) (mults (A:=A) multA (n:=n) a p))); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a p)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) b q) 
                  (multpf p q)))); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pX (multTerm (A:=A) multA (n:=n) b a) (pO A n))
               (mults (A:=A) multA (n:=n) a p))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) b q) 
               (multpf p q))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) a (pX b p))) in |- *;
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pX (multTerm (A:=A) multA (n:=n) a b) (pO A n))
            (mults (A:=A) multA (n:=n) a p)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply pluspf_pX; auto.
change (canonical A0 eqA ltM (mults (A:=A) multA (n:=n) a (pX b p))) in |- *;
 auto.
Qed.
 
Theorem multpf_head :
 forall (p q : list (Term A n)) (a b : Term A n),
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX b q) ->
 exists c : list (Term A n),
   multpf (pX a p) (pX b q) = pX (multTerm (A:=A) multA (n:=n) a b) c.
intros p; elim p; clear p; auto.
simpl in |- *; intros q a b H' H'0.
cut (canonical A0 eqA ltM q);
 [ intros Op0 | apply canonical_imp_canonical with (a := b) ]; 
 auto.
exists (mults (A:=A) multA (n:=n) a q); simpl in |- *; auto.
rewrite <- pO_pluspf_inv2; auto.
intros a1 p H' q a0 b H'0 H'1; auto.
elim (H' q a1 b); simpl in |- *; [ intros c E | idtac | idtac ]; auto.
2: apply canonical_imp_canonical with (a := a0); auto.
rewrite E.
exists
 (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
    (mults (A:=A) multA (n:=n) a0 q)
    (pX (multTerm (A:=A) multA (n:=n) a1 b) c)); auto.
rewrite <- pluspf_inv1_eq; auto.
apply multTerm_ltT_r; auto.
apply (canonical_pX_order _ A0 eqA) with (l := p); auto.
Qed.
 
Theorem in_multpf_head :
 forall (p q : list (Term A n)) (a b : Term A n),
 canonical A0 eqA ltM (pX a p) ->
 canonical A0 eqA ltM (pX b q) ->
 In (multTerm (A:=A) multA (n:=n) a b) (multpf (pX a p) (pX b q)).
intros p q a b H' H'0.
elim (multpf_head p q a b); [ intros c E; rewrite E | idtac | idtac ];
 simpl in |- *; auto.
Qed.
 
Theorem multpf_comp :
 forall p r : list (Term A n),
 eqP A eqA n p r ->
 forall q s : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 canonical A0 eqA ltM s ->
 eqP A eqA n q s -> eqP A eqA n (multpf p q) (multpf r s).
intros p r H'; elim H'; simpl in |- *; auto.
intros ma mb p0 q H'0 H'1 H'2 q0 s H'3 H'4 H'5 H'6 H'7.
cut (canonical A0 eqA ltM p0);
 [ intros Op0 | apply canonical_imp_canonical with (a := ma); auto ].
cut (canonical A0 eqA ltM q);
 [ intros Op1 | apply canonical_imp_canonical with (a := mb); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) ma);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := p0); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) mb);
 [ intros Z1 | apply canonical_nzeroP with (ltM := ltM) (p := q) ]; 
 auto.
Qed.
 
Theorem multpf_com :
 forall p q : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q -> eqP A eqA n (multpf p q) (multpf q p).
intros p; elim p; simpl in |- *; auto.
intros q; elim q; simpl in |- *; auto.
intros a l H' H'0 H'1.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pO A n) (pO A n)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' q H'0 H'1.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a q) (multpf q l)); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
change
  (eqP A eqA n (multpf q (pX a l))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (mults (A:=A) multA (n:=n) a q) (multpf q l))) 
 in |- *.
apply multpf_disr_pX; auto.
Qed.
 
Theorem multpf_dist_plusr :
 forall (p q r : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 eqP A eqA n
   (multpf
      (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p
         q) r)
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (multpf p r) (multpf q r)).
intros p q r; elim r.
intros H' H'0 H'1 H'2.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multpf (pO A n)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec p q)); auto.
apply multpf_com; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (multpf (pO A n) p) (multpf (pO A n) q)); 
 auto.
simpl in |- *; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto; apply multpf_com; auto.
intros a l H' H'0 H'1 H'2 H'3.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec p q))
            (multpf
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec p q) l)); auto.
change
  (eqP A eqA n
     (multpf
        (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
           p q) (pX a l))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (mults (A:=A) multA (n:=n) a
           (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
              ltM_dec p q))
        (multpf
           (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
              ltM_dec p q) l))) in |- *.
apply multpf_disr_pX; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a p)
               (mults (A:=A) multA (n:=n) a q))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (multpf p l) (multpf q l))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a q)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (multpf p l) (multpf q l)))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) a q) 
                  (multpf p l)) (multpf q l))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (multpf p l) (mults (A:=A) multA (n:=n) a q))
               (multpf q l))); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a p)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (multpf p l)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (mults (A:=A) multA (n:=n) a q) 
                  (multpf q l)))); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a p) 
               (multpf p l))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults (A:=A) multA (n:=n) a q) 
               (multpf q l))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply eqp_pluspf_com with (1 := cs); auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (mults (A:=A) multA (n:=n) a p) (multpf p l)) 
     (multpf p (pX a l))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply multpf_disr_pX; auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (mults (A:=A) multA (n:=n) a q) (multpf q l)) 
     (multpf q (pX a l))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply multpf_disr_pX; auto.
Qed.
 
Theorem multpf_dist_plusl :
 forall (p q r : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 eqP A eqA n
   (multpf p
      (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec q
         r))
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (multpf p q) (multpf p r)).
intros p q r H' H'0 H'1 H'2.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := multpf
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec q r) p); auto.
apply multpf_com; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (multpf q p) (multpf r p)); auto.
apply multpf_dist_plusr; auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply multpf_com; auto.
apply multpf_com; auto.
Qed.
 
Theorem multpf_smultm_assoc :
 forall (p q : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 eqP A eqA n (mults (A:=A) multA (n:=n) a (multpf p q))
   (multpf (mults (A:=A) multA (n:=n) a p) q).
intros p q a; elim p; simpl in |- *; auto.
intros a0 l H' H'0 H'1 H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0);
 [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a0) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) a0 q))
            (mults (A:=A) multA (n:=n) a (multpf l q))); 
 auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Theorem multpf_assoc :
 forall p q r : list (Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 canonical A0 eqA ltM r ->
 eqP A eqA n (multpf p (multpf q r)) (multpf (multpf p q) r).
intros p q r; elim p; simpl in |- *; auto.
intros a l H' H'0 H'1 H'2.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZ0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
cut (canonical A0 eqA ltM l);
 [ intros Op0 | apply canonical_imp_canonical with (a := a) ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (multpf (mults (A:=A) multA (n:=n) a q) r)
            (multpf (multpf l q) r)); auto.
apply eqp_pluspf_com with (1 := cs); auto.
apply multpf_smultm_assoc; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multpf_dist_plusr; auto.
Qed.
 
Definition smult : poly A0 eqA ltM -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros sp1 sp2.
case sp1; case sp2.
intros p1 H'1 p2 H'2; exists (multpf p1 p2); auto.
Defined.
End Pmult.