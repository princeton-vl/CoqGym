(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : multiplication by a scalar                     
                                                                           
          Laurent Thery March 98 (revised Avril 01)                          
                                                                           
  ***************************************************************************
   definition of Pmults*)

Require Export Pplus.
Section Pmults.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hPlus".
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition mults : Term A n -> list (Term A n) -> list (Term A n).
intros a p; elim p; clear p.
exact (pO A n).
intros b p1 p'1.
exact (pX (multTerm (A:=A) multA (n:=n) a b) p'1).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Hint Resolve multTerm_eqT.
Hint Resolve invTerm_eqT.
Hint Resolve T1_is_min_ltT.
 
Lemma mults_order_l :
 forall l m1 m2,
 ~ zeroP (A:=A) A0 eqA (n:=n) m1 ->
 canonical A0 eqA ltM (pX m2 l) ->
 canonical A0 eqA ltM (pX (multTerm (A:=A) multA (n:=n) m1 m2) (mults m1 l)).
intros l; elim l; simpl in |- *; auto.
intros m1 m2 H' H'0.
apply canonicalp1; auto.
red in |- *; intros H'1; apply H'.
elim multTerm_zeroP_div with (1 := cs) (a := m1) (b := m2); auto; intros H'5.
absurd (zeroP (A:=A) A0 eqA (n:=n) m2); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pO A n); auto.
intros a l0 H' m1 m2 H'0 H'1.
apply canonical_cons; auto.
apply multTerm_ltT_l; auto.
apply (canonical_pX_order A A0 eqA) with (l := l0); auto.
red in |- *; intros H'2; apply H'0.
elim multTerm_zeroP_div with (1 := cs) (a := m1) (b := m2); auto; intros H'5.
absurd (zeroP (A:=A) A0 eqA (n:=n) m2); auto.
apply canonical_nzeroP with (ltM := ltM) (p := pX a l0); auto.
apply H'; auto.
apply canonical_imp_canonical with (a := m2); auto.
Qed.
 
Lemma canonical_mults :
 forall m l,
 ~ zeroP (A:=A) A0 eqA (n:=n) m ->
 canonical A0 eqA ltM l -> canonical A0 eqA ltM (mults m l).
intros m l; elim l; simpl in |- *; auto.
intros a l0 H' H'0 H'1.
apply mults_order_l; auto.
Qed.

Lemma canonical_mults_inv :
 forall (p : list (Term A n)) (a : Term A n),
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 canonical A0 eqA ltM (mults a p) -> canonical A0 eqA ltM p.
intros p; elim p; simpl in |- *; auto.
intros a l; case l; simpl in |- *; auto.
intros H' a0 H'0 H'1.
change (canonical A0 eqA ltM (pX a (pO A n))) in |- *; apply canonicalp1;
 auto.
red in |- *; intros H'2;
 absurd (zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a));
 auto.
apply canonical_nzeroP with (ltM := ltM) (p := pO A n); auto.
intros a0 l0 H' a1 H'0 H'1.
change (canonical A0 eqA ltM (pX a (pX a0 l0))) in |- *.
apply canonical_cons; auto.
case (ltT_dec A n ltM ltM_dec a0 a);
 [ intros temp; case temp; clear temp | idtac ]; intros H; 
 auto.
absurd
 (ltT ltM (multTerm (A:=A) multA (n:=n) a1 a)
    (multTerm (A:=A) multA (n:=n) a1 a0)); auto.
apply ltT_not_ltT; auto.
apply (canonical_pX_order A A0 eqA) with (l := mults a1 l0); auto.
apply multTerm_ltT_l with (1 := os); auto.
absurd
 (ltT ltM (multTerm (A:=A) multA (n:=n) a1 a0)
    (multTerm (A:=A) multA (n:=n) a1 a)); auto.
apply (canonical_pX_order A A0 eqA) with (l := mults a1 l0); auto.
red in |- *; intros H'2;
 absurd (zeroP (A:=A) A0 eqA (n:=n) (multTerm (A:=A) multA (n:=n) a1 a));
 auto.
apply canonical_nzeroP with (ltM := ltM) (p := mults a1 l0); auto.
apply canonical_skip_fst with (b := multTerm (A:=A) multA (n:=n) a1 a0); auto.
apply H' with (a := a1); auto.
apply canonical_imp_canonical with (a := multTerm (A:=A) multA (n:=n) a1 a);
 auto.
Qed.

Set Implicit Arguments.
Unset Strict Implicit.
 
Definition tmults : Term A n -> list (Term A n) -> list (Term A n).
intros a; case (zeroP_dec A A0 eqA eqA_dec n a); intros Z0.
intros H'; exact (pO A n).
intros p; exact (mults a p).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem tmults_zerop_eqp_pO :
 forall p a,
 zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n (tmults a p) (pO A n).
intros p a; unfold tmults in |- *; case (zeroP_dec A A0 eqA eqA_dec n a);
 auto.
intros H' H'0; elim H'; auto.
Qed.
 
Theorem mults_eqp_pO_pO :
 forall p a, eqP A eqA n p (pO A n) -> eqP A eqA n (mults a p) (pO A n).
unfold pO in |- *; intros p a H'; inversion H'; auto.
Qed.
 
 
Theorem eqp_invT1_pO_is_pO :
 forall p : list (Term A n),
 eqP A eqA n (mults (invTerm (A:=A) invA (n:=n) (T1 A1 n)) p) (pO A n) ->
 eqP A eqA n p (pO A n).
intros p; case p; simpl in |- *; auto.
intros a l H'; inversion H'.
Qed.
 

Theorem mults_eqp_zpO :
 forall a : Term A n,
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 forall p : list (Term A n),
 eqP A eqA n (mults a p) (pO A n) -> eqP A eqA n p (pO A n).
intros a H' p; elim p; simpl in |- *; auto.
intros a0 l H'0 H'1; inversion H'1; auto.
Qed.

Theorem mults_dist1 :
 forall p a b,
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 ~ zeroP (A:=A) A0 eqA (n:=n) b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 canonical A0 eqA ltM p ->
 eqP A eqA n (mults (plusTerm (A:=A) plusA (n:=n) a b) p)
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (mults a p) (mults b p)).
intros p; elim p; simpl in |- *; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n);
 apply p0_pluspf_l with (1 := cs); auto.
intros a l H' a0 b H'0 H'1 H'2 H'3 H'4.
cut (canonical A0 eqA ltM l); try apply canonical_imp_canonical with (a := a);
 auto; intros C0.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a)
               (multTerm (A:=A) multA (n:=n) b a))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults a0 l) (mults b l))); 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a)
               (multTerm (A:=A) multA (n:=n) b a))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults a0 l) (mults b l))); 
 auto.
apply (eqpP1 _ eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply multTerm_plusTerm_dist_l with (1 := cs); auto.
apply pluspf_inv3b with (1 := cs); auto.
red in |- *; intros H'5;
 absurd
  (zeroP (A:=A) A0 eqA (n:=n)
     (multTerm (A:=A) multA (n:=n) (plusTerm (A:=A) plusA (n:=n) a0 b) a));
 auto.
red in |- *; intros H'6.
elim
 multTerm_zeroP_div
  with (1 := cs) (a := plusTerm (A:=A) plusA (n:=n) a0 b) (b := a); 
 auto.
intros H'7; absurd (zeroP (A:=A) A0 eqA (n:=n) a); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a)
            (multTerm (A:=A) multA (n:=n) b a)); auto.
apply multTerm_plusTerm_dist_l with (1 := cs); auto.
Qed.
 
Theorem mults_dist2 :
 forall (p : list (Term A n)) (a b : Term A n),
 eqT a b ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 ~ zeroP (A:=A) A0 eqA (n:=n) b ->
 zeroP (A:=A) A0 eqA (n:=n) (plusTerm (A:=A) plusA (n:=n) a b) ->
 canonical A0 eqA ltM p ->
 eqP A eqA n (pO A n)
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (mults a p) (mults b p)).
intros p; elim p; simpl in |- *; auto.
intros; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l H' a0 b H'0 H'1 H'2 H'3 H'4.
cut (canonical A0 eqA ltM l); try apply canonical_imp_canonical with (a := a);
 auto; intros C0.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults a0 l) (mults b l)); auto.
apply pluspf_inv3a with (1 := cs); auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := multTerm (A:=A) multA (n:=n) (plusTerm (A:=A) plusA (n:=n) a0 b) a);
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply multTerm_plusTerm_dist_l with (1 := cs); auto.
Qed.
 
Theorem mults_T1 :
 forall (p : list (Term A n)) (a : Term A n),
 eqTerm (A:=A) eqA (n:=n) a (T1 A1 n) -> eqP A eqA n (mults a p) p.
intros p; elim p; auto.
simpl in |- *; auto.
intros a l H a0 H0;
 change
   (eqP A eqA n (pX (multTerm (A:=A) multA (n:=n) a0 a) (mults a0 l))
      (pX a l)) in |- *; auto.
apply (eqpP1 A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply T1_multTerm_l with (1 := cs);
 auto.
Qed.
 
Theorem mults_invTerm :
 forall (p : list (Term A n)) (a : Term A n),
 eqTerm (A:=A) eqA (n:=n) a (T1 A1 n) ->
 eqP A eqA n
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p
      (mults (invTerm (A:=A) invA (n:=n) a) p)) (pO A n).
intros p; elim p; simpl in |- *; auto.
intros a l H' a0 H'0.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            l (mults (invTerm (A:=A) invA (n:=n) a0) l)); 
 auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a l)
        (pX (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) a0) a)
           (mults (invTerm (A:=A) invA (n:=n) a0) l)))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l
        (mults (invTerm (A:=A) invA (n:=n) a0) l))) 
 in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply pluspf_inv3a with (1 := cs);
 auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) a0 a); auto.
apply (T1_eqT _ A1 eqA); auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := plusTerm (A:=A) plusA (n:=n) a (invTerm (A:=A) invA (n:=n) a));
 auto.
apply plusTerm_invTerm_zeroP with (1 := cs); auto.
apply plusTerm_comp_r with (1 := cs); auto.
change
  (eqT a (multTerm (A:=A) multA (n:=n) (invTerm (A:=A) invA (n:=n) a0) a))
 in |- *.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a);
 auto.
apply (T1_eqT _ A1 eqA); auto.
apply multTerm_eqT; auto.
apply (eqT_trans A n) with (y := a0); auto.
apply (eqT_sym A n); auto.
apply (eqTerm_imp_eqT A eqA); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := invTerm (A:=A) invA (n:=n)
            (multTerm (A:=A) multA (n:=n) a (T1 A1 n))); 
 auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) a a0));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply eqTerm_invTerm_comp with (1 := cs); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := invTerm (A:=A) invA (n:=n) (multTerm (A:=A) multA (n:=n) a0 a));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply mult_invTerm_com with (1 := cs); auto.
Qed.
 
Theorem mults_multTerm :
 forall (p : list (Term A n)) (a b : Term A n),
 eqP A eqA n (mults (multTerm (A:=A) multA (n:=n) a b) p)
   (mults a (mults b p)).
intros p; elim p; simpl in |- *; auto.
intros a l H a0 b; apply (eqpP1 A eqA n); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply multTerm_assoc with (1 := cs); auto.
Qed.
 
Theorem mults_com :
 forall (p : list (Term A n)) (a b : Term A n),
 eqP A eqA n (mults (multTerm (A:=A) multA (n:=n) a b) p)
   (mults (multTerm (A:=A) multA (n:=n) b a) p).
intros p; elim p; simpl in |- *; auto.
Qed.
 
Theorem mults_comp :
 forall (a b : Term A n) (p q : list (Term A n)),
 eqTerm (A:=A) eqA (n:=n) a b ->
 eqP A eqA n p q -> eqP A eqA n (mults a p) (mults b q).
intros a b p q H' H'0; elim H'0; simpl in |- *; auto.
Qed.
 
Theorem mults_ltP_comp :
 forall (a : Term A n) (p q : list (Term A n)),
 ltP (A:=A) (n:=n) ltM p q -> ltP (A:=A) (n:=n) ltM (mults a p) (mults a q).
intros a p q H'; elim H'; simpl in |- *; auto.
intros x y p0 q0 H'0; simpl in |- *; apply ltP_hd; auto.
apply multTerm_ltT_l with (1 := os); auto.
Qed.
 
 
Theorem multlm_comp_canonical :
 forall (p : list (Term A n)) (a b : Term A n),
 canonical A0 eqA ltM (pX a p) ->
 ~ zeroP (A:=A) A0 eqA (n:=n) b ->
 canonical A0 eqA ltM (pX (multTerm (A:=A) multA (n:=n) b a) (mults b p)).
intros p a b H' H'0; generalize (canonical_mults b (pX a p)); simpl in |- *;
 auto.
Qed.
Hint Resolve multlm_comp_canonical.
 
Let ffst := fst (A:=list (Term A n)) (B:=list (Term A n)).
 
Let ssnd := snd (A:=list (Term A n)) (B:=list (Term A n)).
 
Let ppair := pair (A:=list (Term A n)) (B:=list (Term A n)).
 
Definition twoP_ind :
  forall P : list (Term A n) -> list (Term A n) -> Prop,
  (forall p q : list (Term A n),
   (forall r s : list (Term A n), lessP A n (r, s) (p, q) -> P r s) -> P p q) ->
  forall p q : list (Term A n), P p q.
intros P H' p q; try assumption.
change
  ((fun pq : list (Term A n) * list (Term A n) => P (ffst pq) (ssnd pq))
     (p, q)) in |- *.
cut (exists x : list (Term A n) * list (Term A n), x = ppair p q).
unfold ppair in |- *; intros H'0; elim H'0; intros x E; rewrite <- E;
 clear H'0.
pattern x in |- *;
 apply
  well_founded_ind
   with
     (A := (list (Term A n) * list (Term A n))%type)
     (R := lessP A n)
     (1 := wf_lessP A n); auto.
intros x0 H'0; apply H'; auto.
intros r s H'1.
apply (H'0 (r, s)).
generalize H'1; case x0; simpl in |- *; auto.
exists (ppair p q); auto.
Qed.
 
Theorem mults_dist_pluspf :
 forall (p q : list (Term A n)) (a : Term A n),
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 eqP A eqA n
   (mults a
      (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec p
         q))
   (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
      (mults a p) (mults a q)).
intros p q; pattern p, q in |- *.
apply twoP_ind; simpl in |- *; auto.
intros p0; case p0; simpl in |- *; auto.
intros q0 H' a H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults a q0); auto.
apply mults_comp; auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pO A n) q0) q0) in |- *; auto.
change
  (eqP A eqA n (mults a q0)
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pO A n) (mults a q0))) in |- *; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros a l q0.
case q0; simpl in |- *; auto.
intros H' a0 H'0 H'1 H'2.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mults a0 (pX a l)); auto.
apply mults_comp; auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a l) (pO A n)) (pX a l)) in |- *; auto.
change
  (eqP A eqA n (mults a0 (pX a l))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX (multTerm multA a0 a) (mults a0 l)) (pO A n))) 
 in |- *; simpl in |- *; apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); 
 auto.
intros a0 l0 H' a1 H'0 H'1 H'2; simpl in |- *.
case (ltT_dec A n ltM ltM_dec a a0); [ intros H0; case H0; clear H0 | idtac ];
 intros H0.
cut
 (ltT ltM (multTerm (A:=A) multA (n:=n) a1 a)
    (multTerm (A:=A) multA (n:=n) a1 a0)); [ intros Od0 | idtac ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults a1
            (pX a0
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec (pX a l) l0))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp; auto.
change
  (eqP A eqA n
     (pX a0
        (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
           (pX a l) l0))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a l) (pX a0 l0))) in |- *.
auto.
apply pluspf_inv2 with (1 := cs); auto.
simpl in |- *.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX (multTerm (A:=A) multA (n:=n) a1 a0)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (pX (multTerm (A:=A) multA (n:=n) a1 a) (mults a1 l))
               (mults a1 l0))); auto.
apply eqpP1; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults a1 (pX a l)) (mults a1 l0)); auto.
apply H'; simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
apply canonical_imp_canonical with (a := a0); auto.
apply pluspf_inv2 with (1 := cs); auto.
apply multTerm_ltT_l; auto.
cut
 (ltT ltM (multTerm (A:=A) multA (n:=n) a1 a0)
    (multTerm (A:=A) multA (n:=n) a1 a)); [ intros Od0 | idtac ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults a1
            (pX a
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec l (pX a0 l0)))); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp; auto.
change
  (eqP A eqA n
     (pX a
        (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
           l (pX a0 l0)))
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a l) (pX a0 l0))) in |- *.
apply pluspf_inv1 with (1 := cs); auto.
simpl in |- *.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX (multTerm (A:=A) multA (n:=n) a1 a)
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults a1 l)
               (pX (multTerm (A:=A) multA (n:=n) a1 a0) (mults a1 l0))));
 auto.
apply eqpP1; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults a1 l) (mults a1 (pX a0 l0))); auto.
apply H'; simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; auto.
apply canonical_imp_canonical with (a := a); auto.
apply pluspf_inv1 with (1 := cs); auto.
apply multTerm_ltT_l; auto.
cut
 (eqT (multTerm (A:=A) multA (n:=n) a1 a)
    (multTerm (A:=A) multA (n:=n) a1 a0)); [ intros Od0 | idtac ]; 
 auto.
case (zeroP_dec A A0 eqA eqA_dec n (plusTerm (A:=A) plusA (n:=n) a a0));
 intros Z0.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults a1
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec l l0)); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp; auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec l
        l0)
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a l) (pX a0 l0))) in |- *; auto.
apply pluspf_inv3a with (1 := cs); auto.
cut
 (zeroP (A:=A) A0 eqA (n:=n)
    (plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) a1 a)
       (multTerm (A:=A) multA (n:=n) a1 a0))); [ intros Od1 | idtac ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
            (mults a1 l) (mults a1 l0)); auto.
apply H'; simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a0); auto.
apply pluspf_inv3a with (1 := cs); auto.
apply
 zeroP_comp_eqTerm
  with
    (1 := cs)
    (a := multTerm (A:=A) multA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a a0)).
apply zeroP_multTerm_r with (1 := cs); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply multTerm_plusTerm_dist_r with (1 := cs); auto.
cut
 (~
  zeroP (A:=A) A0 eqA (n:=n)
    (plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) a1 a)
       (multTerm (A:=A) multA (n:=n) a1 a0))); [ intros Od1 | idtac ]; 
 auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults a1
            (pX (plusTerm (A:=A) plusA (n:=n) a a0)
               (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
                  ltM_dec l l0))); auto.
apply mults_comp; auto.
change
  (eqP A eqA n
     (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
        (pX a l) (pX a0 l0))
     (pX (plusTerm (A:=A) plusA (n:=n) a a0)
        (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM) ltM_dec
           l l0))) in |- *.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply pluspf_inv3b with (1 := cs);
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := pX
            (plusTerm (A:=A) plusA (n:=n) (multTerm (A:=A) multA (n:=n) a1 a)
               (multTerm (A:=A) multA (n:=n) a1 a0))
            (pluspf (A:=A) A0 (eqA:=eqA) plusA eqA_dec (n:=n) (ltM:=ltM)
               ltM_dec (mults a1 l) (mults a1 l0))); 
 auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply pluspf_inv3b with (1 := cs);
 auto.
simpl in |- *.
apply eqpP1; auto.
apply multTerm_plusTerm_dist_r with (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply H'; simpl in |- *; auto.
red in |- *; red in |- *; simpl in |- *; rewrite <- plus_n_Sm; auto.
apply canonical_imp_canonical with (a := a); auto.
apply canonical_imp_canonical with (a := a0); auto.
apply
 nzeroP_comp_eqTerm
  with
    (1 := cs)
    (a := multTerm (A:=A) multA (n:=n) a1 (plusTerm (A:=A) plusA (n:=n) a a0));
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n);
 apply multTerm_plusTerm_dist_r with (1 := cs); auto.
Qed.
Hint Resolve mults_dist_pluspf.

Definition smults : Term A n -> poly A0 eqA ltM -> poly A0 eqA ltM.
intros a sp1.
case sp1.
intros p1 H'1; exists (tmults a p1); auto.
unfold tmults in |- *; case (zeroP_dec A A0 eqA eqA_dec n a); simpl in |- *;
 auto.
intros; apply canonical_mults; auto.
Defined.

End Pmults.