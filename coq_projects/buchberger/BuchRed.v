(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export Pcomb.
Require Export Pcrit.
Require Export Buch.
Require Export Fred.
Require Import Buch.

Local Unset Injection On Proofs.

Section BuchRed.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hBuch".
 
Theorem Cb_addEnd_cons :
 forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (addEnd A A0 eqA n ltM p L) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L).
intros L p q H; apply Cb_incl with (1 := cs) (P := addEnd A A0 eqA n ltM p L);
 auto.
elim L; simpl in |- *; auto.
intros a l H0 a0 H1; elim H1; clear H1; intros H1; auto.
case (H0 a0); auto.
Qed.
 
Theorem Cb_cons_addEnd :
 forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (addEnd A A0 eqA n ltM p L).
intros L p q H; apply Cb_incl with (1 := cs) (P := p :: L); auto.
elim L; simpl in |- *; auto.
intros a l H0 a0 H1; elim H1; clear H1; intros H1; auto.
case H1; auto.
Qed.
 
Theorem Cb_trans_cons :
 forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
intros L p q H H0.
apply Cb_trans with (1 := cs) (b := p); auto.
apply Cb_cons_addEnd; auto.
Qed.
 
Theorem Cb_cons :
 forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p
      L) (p :: L).
intros p L; unfold nf, LetP in |- *; auto.
case
 (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
    os L p); simpl in |- *; auto.
intros x0; case x0; simpl in |- *.
intros x c H'.
change
  (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec 
     (p :: L)
     (mults (A:=A) multA (n:=n)
        (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x c)) x)) 
 in |- *.
apply CombLinear_mults1 with (1 := cs); auto.
apply unit_nZ with (1 := cs); auto.
apply reducestar_cb1 with (1 := cs); auto.
Qed.
 
Theorem Cb_comp :
 forall L1 L2 : list (poly A0 eqA ltM),
 (forall p : poly A0 eqA ltM,
  In p L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L2) ->
 forall q : poly A0 eqA ltM,
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L1 ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L2.
intros L1 L2 H' q; case q; simpl in |- *.
intros x H'0 H'1.
apply CombLinear_compo with (1 := cs) (L1 := L1); auto.
intros q0 H'2.
case inPolySet_inv1 with (1 := H'2); auto.
intros q1 H; elim H; intros H0 H1; clear H.
lapply (H' q1); [ intros H'6 | idtac ]; auto.
generalize H'6 H1; case q1; simpl in |- *; auto.
intros x0 H'5 H'7 H'8; rewrite H'8; auto.
Defined.
 
Theorem Cb_nf :
 forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p
      L :: L).
intros p L; unfold nf in |- *.
case
 (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
    os L p); auto.
case p.
unfold LetP in |- *; intros x H' x0; case x0; simpl in |- *.
intros x1 c H'0.
change
  (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec
     (mks A A0 eqA n ltM
        (mults (A:=A) multA (n:=n)
           (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c)) x1)
        (canonical_mults A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec
           n ltM os (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c))
           x1
           (unit_nZ A A0 A1 eqA plusA invA minusA multA divA cs n ltM
              (mks A A0 eqA n ltM x1 c)) c) :: L) x) 
 in |- *.
apply CombLinear_compo with (1 := cs) (L1 := mks A A0 eqA n ltM x1 c :: L);
 auto.
change
  (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec
     (mks A A0 eqA n ltM x1 c :: L)
     (s2p A A0 eqA n ltM (mks A A0 eqA n ltM x H'))) 
 in |- *.
apply reducestar_cb2 with (1 := cs); auto.
intros q H'1; inversion H'1; auto.
2: apply CombLinear_id with (1 := cs); auto.
2: apply inskip; auto.
generalize c H2; case x1; auto.
intros c0 H'2; inversion H'2.
intros a0 l c0 H'2.
cut
 (~
  zeroP (A:=A) A0 eqA (n:=n)
    (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)));
 [ intros nZu | idtac ]; auto.
apply
 CombLinear_1
  with
    (a := divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
            (T1 A1 n)
            (b:=unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0))
            nZu)
    (p := pO A n)
    (q := mults (A:=A) multA (n:=n)
            (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0))
            (pX a0 l)); auto.
simpl in |- *; auto.
change
  (inPolySet A A0 eqA n ltM
     (pX
        (multTerm (A:=A) multA (n:=n)
           (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) a0)
        (mults (A:=A) multA (n:=n)
           (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0)) l))
     (exist (fun a1 => canonical A0 eqA ltM a1)
        (pX
           (multTerm (A:=A) multA (n:=n)
              (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))
              a0)
           (mults (A:=A) multA (n:=n)
              (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))
              l))
        (canonical_mults A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec
           n ltM os
           (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a0 l) c0))
           (pX a0 l)
           (unit_nZ _ _ _ _ _ _ _ _ _ cs _ ltM
              (mks A A0 eqA n ltM (pX a0 l) c0)) c0) :: L)) 
 in |- *.
apply incons; auto.
apply CombLinear_0; auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
               (T1 A1 n)
               (b:=unit A A0 A1 eqA divA n ltM
                     (mks A A0 eqA n ltM (a0 :: l) c0)) nZu)
            (mults (A:=A) multA (n:=n)
               (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0))
               (a0 :: l))); auto.
2: apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with
    (y := mults (A:=A) multA (n:=n)
            (multTerm (A:=A) multA (n:=n)
               (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) 
                  (T1 A1 n)
                  (b:=unit A A0 A1 eqA divA n ltM
                        (mks A A0 eqA n ltM (a0 :: l) c0)) nZu)
               (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (a0 :: l) c0)))
            (a0 :: l)); auto.
apply
 (eqp_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := mults (A:=A) multA (n:=n) (T1 A1 n) (a0 :: l)); 
 auto.
rewrite H'2; auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply mults_comp with (1 := cs); auto.
apply divTerm_on_eqT with (1 := cs); auto.
apply (eqT_sym A n); auto.
apply unit_T1; auto.
apply unit_nZ with (1 := cs); auto.
Qed.
 
Theorem zerop_elim_Cb :
 forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM),
 zerop A A0 eqA n ltM p ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
intros L p q H' H'0.
apply Cb_comp with (L1 := p :: L); auto.
simpl in |- *; auto.
intros p0 H'1; case H'1;
 [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; 
 auto.
generalize H'; case p; simpl in |- *; auto.
intros x; case x; simpl in |- *; auto.
intros H'1 H'3; try assumption.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec L (pO A n))
 in |- *.
apply CombLinear_0; auto.
intros a l H'1 H'3; elim H'3; auto.
apply Cb_id with (1 := cs); auto.
Qed.
 
Theorem Cb_compo :
 forall (p : poly A0 eqA ltM) (L1 : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L1 ->
 forall L2 : list (poly A0 eqA ltM),
 (forall q : poly A0 eqA ltM,
  In q L1 -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L2) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L2.
intros p L1 H' L2 H'0.
apply Cb_comp with (L1 := L1); auto.
Qed.
 
Definition reducep (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM) :
  Prop :=
  reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec L
    (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM q).
 
Theorem grobner_def :
 forall L : list (poly A0 eqA ltM),
 Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L ->
 forall p : poly A0 eqA ltM,
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L ->
 zerop A A0 eqA n ltM p \/ (exists q : poly A0 eqA ltM, reducep L p q).
intros L H'; inversion H'; auto.
intros p H'0.
case
 (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
    os L p).
intros x H'1; inversion H'.
lapply (H0 (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM x));
 [ intros H'4; lapply H'4; [ clear H'4 | clear H'4 ] | idtac ]; 
 auto.
inversion H'1; auto.
inversion H1; auto.
intros H'2; left.
cut (eqP A eqA n (s2p A A0 eqA n ltM p) (pO A n)); auto.
case p; simpl in |- *; auto.
intros x1; case x1; auto.
intros a l H'3 H'4; inversion H'4.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := s2p A A0 eqA n ltM x);
 auto.
intros H'2; right; cut (canonical A0 eqA ltM y); auto.
intros H'3; exists (mks A A0 eqA n ltM y H'3); generalize H5; case p;
 simpl in |- *; auto.
apply canonical_reduce with (1 := cs) (3 := H5); auto.
generalize H'0; case p; simpl in |- *; auto.
generalize H'0; case p; simpl in |- *; auto.
Qed.
 
Theorem def_grobner :
 forall L : list (poly A0 eqA ltM),
 (forall p : poly A0 eqA ltM,
  Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L ->
  zerop A A0 eqA n ltM p \/ (exists q : poly A0 eqA ltM, reducep L p q)) ->
 Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L.
intros L H'.
apply Grobner0.
intros p q H'0 H'1.
cut (canonical A0 eqA ltM p).
intros H'2.
cut (canonical A0 eqA ltM q).
intros H'3.
elim (H' (mks A A0 eqA n ltM q H'3)); [ intros H'6 | intros H'6 | idtac ];
 auto.
generalize H'3 H'6; case q; simpl in |- *; auto.
intros a l H'4 H'5; elim H'5; auto.
case H'6; intros q0 E; clear H'6.
inversion H'1.
generalize H0 E; case q0; auto.
simpl in |- *; auto.
intros x H'4 H'5 H'6;
 absurd
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec L q x);
 auto.
simpl in |- *; auto.
apply reducestar_cb with (a := p) (1 := cs); auto.
inversion H'1.
apply canonical_reduceplus with (1 := cs) (3 := H); auto.
apply CombLinear_canonical with (1 := cs) (3 := H'0); auto.
Qed.
 
Theorem reduce_divp :
 forall (p q : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM q) ->
 exists r : poly A0 eqA ltM,
   In r (q :: Q) /\
   divp A A0 eqA multA divA n ltM p r /\ ~ zerop A A0 eqA n ltM r.
intros p q; case p; case q; simpl in |- *.
intros x H' x0 c Q H'0; inversion H'0.
generalize c; rewrite <- H2; simpl in |- *; auto.
case inPolySet_inv1 with (1 := H); auto.
intros q1 E; case E; intros H'1 H'2; clear E.
intros c0; exists q1; split; [ right | split ]; auto.
generalize H'2; case q1; simpl in |- *; auto.
intros x1; case x1; auto.
intros H'4 H'5; discriminate H'5; auto.
intros a0 l H'4 H'5; injection H'5; intros.
rewrite <- H5; trivial.
generalize H'1 H'2 c0; case q1; simpl in |- *; auto.
intros x1; case x1; auto.
intros c1 H'3 H'4; discriminate H'4.
exists (exist (fun l : list (Term A n) => canonical A0 eqA ltM l) x H');
 split; [ left | split ]; simpl in |- *; auto.
generalize c; rewrite <- H1; unfold pX in |- *; auto.
generalize H'; rewrite <- H2; unfold pX in |- *; auto.
intros H'1 H'2.
apply divP_eqTerm_comp with (a := b) (1 := cs); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) b); [ intros Z | idtac ]; auto.
apply divTerm_def with (nZb := Z); auto.
apply canonical_nzeroP with (ltM := ltM) (p := q0); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
generalize c H'; rewrite <- H2; auto.
Qed.
 
Theorem reduceplus_divp_lem :
 forall (a b : list (Term A n)) (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q a b ->
 canonical A0 eqA ltM a ->
 forall x y : poly A0 eqA ltM,
 s2p A A0 eqA n ltM x = a ->
 s2p A A0 eqA n ltM y = b ->
 ~ zerop A A0 eqA n ltM x ->
 exists r : poly A0 eqA ltM,
   In r (y :: Q) /\
   divp A A0 eqA multA divA n ltM x r /\ ~ zerop A A0 eqA n ltM r.
intros a b Q H'; elim H'; auto.
intros x y H'0 H'1 x0 y0 H'2 H'3 H'4; exists y0; split; [ idtac | split ];
 auto with datatypes.
generalize H'0 H'4; clear H'0 H'4; rewrite <- H'3; rewrite <- H'2; case x0;
 case y0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros H2 x2; case x2; auto.
intros t l H'5 H'6; inversion_clear H'6; auto.
intros t l H'0 x2; case x2; simpl in |- *; auto.
intros t0 l0 H'5 H'6; inversion_clear H'6; auto.
intros H5; apply divP_eqTerm_comp with (a := t) (1 := cs); auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) t); [ intros Z | idtac ]; auto.
apply divTerm_def with (nZb := Z); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
generalize H'0 H'4; clear H'0 H'4; rewrite <- H'3; rewrite <- H'2; case x0;
 case y0; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros H'0 x2; case x2; simpl in |- *; auto.
intros t l H'4 H'5; inversion_clear H'5.
intros x y z H'0 H'1 H'2 H'3 x0 y0 H'4 H'5 H'6.
cut (canonical A0 eqA ltM y); [ intros Z | idtac ].
2: apply canonical_reduce with (1 := cs) (3 := H'0); auto.
lapply (reduce_divp x0 (mks A A0 eqA n ltM y Z) Q); [ intros H'9 | idtac ];
 auto.
2: rewrite H'4; simpl in |- *; auto.
case H'9; intros r E; case E; simpl in |- *; intros H'7 H'8; case H'8;
 intros H'10 H'11; clear H'8 E H'9.
case H'7; [ intros H'8; clear H'7 | intros H'8; clear H'7 ].
2: exists r; split; [ right | idtac ]; auto.
lapply H'2;
 [ intros H'7; lapply (H'7 (mks A A0 eqA n ltM y Z) y0); simpl in |- *;
    [ intros H'13; lapply H'13;
       [ intros H'14; lapply H'14;
          [ intros H'15; clear H'14 H'13 H'2 | clear H'14 H'13 H'2 ]
       | clear H'13 H'2 ]
    | clear H'2 ]
 | clear H'2 ]; auto.
case H'15; intros r0 E; case E; intros H'2 H'9; case H'9; intros H'12 H'13;
 clear H'9 E H'15.
exists r0; split; [ idtac | split ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := r); auto.
rewrite <- H'8; auto.
generalize H'11; rewrite <- H'8.
generalize Z; case y; auto.
Qed.
 
Theorem reduceplus_divp :
 forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) ->
 ~ zerop A A0 eqA n ltM a ->
 exists r : poly A0 eqA ltM,
   In r (b :: Q) /\
   divp A A0 eqA multA divA n ltM a r /\ ~ zerop A A0 eqA n ltM r.
intros a b Q H' H'0.
apply
 reduceplus_divp_lem
  with (a := s2p A A0 eqA n ltM a) (b := s2p A A0 eqA n ltM b); 
 auto.
apply canonical_s2p; auto.
Qed.
 
Theorem reducestar_divp :
 forall (a b : poly A0 eqA ltM) (Q : list (poly A0 eqA ltM)),
 reducestar A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
   (s2p A A0 eqA n ltM a) (s2p A A0 eqA n ltM b) ->
 ~ zerop A A0 eqA n ltM a ->
 exists r : poly A0 eqA ltM,
   In r (b :: Q) /\
   divp A A0 eqA multA divA n ltM a r /\ ~ zerop A A0 eqA n ltM r.
intros a b Q H' H'0; apply reduceplus_divp; auto.
inversion H'; auto.
Qed.
 
Theorem nf_divp :
 forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 ~ zerop A A0 eqA n ltM p ->
 ~
 zerop A A0 eqA n ltM
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p
      L) ->
 exists q : poly A0 eqA ltM,
   In q
     (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
        p L :: L) /\
   divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros p L; case p; unfold nf in |- *; auto.
unfold nf in |- *; auto.
intros x c;
 case
  (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
     os L (exist (fun l => canonical A0 eqA ltM l) x c)).
unfold LetP in |- *.
intros x0; case x0; auto.
intros x1 c0 H' H'0 H'1.
lapply
 (reducestar_divp (mks A A0 eqA n ltM x c) (mks A A0 eqA n ltM x1 c0) L);
 [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ];
 auto.
case H'6; intros r E; case E; intros H'2 H'3; case H'3; intros H'4 H'5;
 clear H'3 E H'6.
case H'2; [ intros H'3; clear H'2 | intros H'3; clear H'2 ].
exists
 (mks A A0 eqA n ltM
    (mults (A:=A) multA (n:=n)
       (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c0)) x1)
    (canonical_mults _ _ _ _ _ _ _ _ _ cs eqA_dec _ _ os
       (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM x1 c0)) x1
       (unit_nZ _ _ _ _ _ _ _ _ _ cs n ltM (mks A A0 eqA n ltM x1 c0)) c0));
 split; [ idtac | split ]; auto.
simpl in |- *; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := r); auto.
generalize H'5; rewrite <- H'3.
generalize c0; case x1; auto.
simpl in |- *; auto.
intros a l c1 H1.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros nZa | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
cut
 (~
  zeroP (A:=A) A0 eqA (n:=n)
    (multTerm (A:=A) multA (n:=n)
       (unit A A0 A1 eqA divA n ltM (mks A A0 eqA n ltM (pX a l) c1)) a));
 [ intros nZu | idtac ]; auto.
simpl in |- *; apply divTerm_def with (nZb := nZu); auto.
apply divTerm_on_eqT with (1 := cs) (a := a); auto.
apply (eqT_trans A n) with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a);
 auto.
apply (eqTerm_imp_eqT A eqA n); auto.
apply multTerm_eqT; auto.
apply (eqT_sym A n); auto.
apply unit_T1; auto.
apply nzeroP_multTerm with (1 := cs); auto.
apply unit_nZ with (1 := cs); auto.
exists r; split; [ idtac | split ]; auto.
simpl in |- *; auto.
Qed.
 
Theorem divp_reduce1 :
 forall (p : poly A0 eqA ltM) (L1 L2 : list (poly A0 eqA ltM)),
 (forall r1 : poly A0 eqA ltM,
  In r1 L1 ->
  ~ zerop A A0 eqA n ltM r1 ->
  exists r2 : poly A0 eqA ltM,
    In r2 L2 /\ divp A A0 eqA multA divA n ltM r1 r2) ->
 forall q : poly A0 eqA ltM,
 reducep L1 p q -> exists r : poly A0 eqA ltM, reducep L2 p r.
intros p L1 L2 H' q; case p; case q; simpl in |- *; auto.
intros x H'0 x0 c H'1; generalize c; unfold reducep in H'1; simpl in H'1;
 elim H'1; auto.
intros a b nZb p0 q0 r H'2 H'3 H'4 c0.
case inPolySet_inv1 with (1 := H'2).
intros q1 E; case E; intros H4 H5; clear E.
elim (H' q1);
 [ intros r2 E; elim E; intros H'10 H'11; clear E | idtac | idtac ]; 
 auto.
generalize H'10 H'11 H5 c0 H4; case q1; simpl in |- *; auto.
intros x1 c1; case r2; simpl in |- *; auto.
intros x2; case x2; simpl in |- *; auto.
generalize c1; case x1; auto.
intros c2 c3 H'6 H'8 H'9 c4 H'12; discriminate.
intros t l c2 c3 H'6 H'8; elim H'8.
intros a0 l c2; generalize c1; case x1; auto.
intros c3 H'6 H'8; elim H'8.
intros t l0 c3 H'6 H'8 H'9 c4 H'12.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros nZa0 | idtac ].
cut
 (canonical A0 eqA ltM
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0
       nZa0 p0 l)); [ intros Z | idtac ].
exists
 (mks A A0 eqA n ltM
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0
       nZa0 p0 l) Z); simpl in |- *; auto.
red in |- *; simpl in |- *; apply reducetop_sp with (1 := cs); auto.
change
  (inPolySet A A0 eqA n ltM
     (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a0 l) c2)) L2) 
 in |- *.
apply in_inPolySet; auto.
simpl in |- *.
red in |- *; intros H'13; inversion H'13.
injection H'9; intros.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
rewrite H0; auto.
apply canonical_spminusf_full with (1 := cs); auto.
injection H'9; intros.
apply (divP_trans _ _ _ _ _ _ _ _ _ cs n) with (y := b); auto.
rewrite H0; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
generalize H5; case q1; simpl in |- *; auto.
intros x1; case x1; simpl in |- *; auto.
intros c1 H'6; discriminate.
intros a b p0 q0 H'2 H'3 H'4 c0.
cut (canonical A0 eqA ltM p0);
 [ intro | apply canonical_imp_canonical with (a := a); auto ].
case (H'3 H); intros r; case r.
intros x1 H'6 H'7.
cut (canonical A0 eqA ltM (pX b x1)); [ intros Z | idtac ].
exists (mks A A0 eqA n ltM (pX b x1) Z); simpl in |- *; auto.
red in |- *; simpl in |- *; red in H'7; simpl in H'7; auto.
apply eqp_imp_canonical with (1 := cs) (p := pX a x1); auto.
apply ltP_pX_canonical; auto.
apply canonical_nzeroP with (ltM := ltM) (p := p0); auto.
apply ltP_trans with (y := p0); auto.
apply ltP_reduce with (1 := cs) (3 := H'7); auto.
apply (canonical_pX_ltP A A0 eqA); auto.
Qed.
 
Theorem nf_divp_zero :
 forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 ~ zerop A A0 eqA n ltM p ->
 zerop A A0 eqA n ltM
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p
      L) ->
 exists q : poly A0 eqA ltM,
   In q L /\ divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros p L; case p; unfold nf in |- *; auto.
unfold nf in |- *; auto.
intros x c;
 case
  (Reducef A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
     os L (exist (fun l : list (Term A n) => canonical A0 eqA ltM l) x c)).
unfold LetP in |- *.
simpl in |- *; intros x0; case x0; simpl in |- *; auto.
intros x1 c0 H' H'0 H'1.
lapply
 (reducestar_divp (mks A A0 eqA n ltM x c) (mks A A0 eqA n ltM x1 c0) L);
 simpl in |- *;
 [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ];
 auto.
case H'6; intros r E; case E; intros H'2 H'3; case H'3; intros H'4 H'5;
 clear H'3 E H'6.
case H'2; [ intros H'3; clear H'2 | intros H'3; clear H'2 ].
case H'5; rewrite <- H'3.
generalize c0 H'1; case x1; auto.
exists r; split; [ idtac | split ]; auto.
Qed.
 
Theorem zerop_elim_cb :
 forall (L : list (poly A0 eqA ltM)) (p q : poly A0 eqA ltM),
 zerop A A0 eqA n ltM p ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q (p :: L) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec q L.
intros L p q H' H'0.
apply Cb_comp with (L1 := p :: L); auto.
simpl in |- *; auto.
intros p0 H'1; case H'1;
 [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; 
 auto.
generalize H'; case p; simpl in |- *; auto.
intros x; case x; simpl in |- *; auto.
intros H'1 H'3; try assumption.
change (CombLinear A A0 eqA plusA multA eqA_dec n ltM ltM_dec L (pO A n))
 in |- *.
apply CombLinear_0; auto.
intros a l H'1 H'3; elim H'3; auto.
apply Cb_id with (1 := cs); auto.
Qed.
 
Theorem zerop_nf_cb :
 forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 zerop A A0 eqA n ltM
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os p
      L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
intros L p H'.
apply
 zerop_elim_cb
  with
    (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os p L); auto.
apply Cb_nf.
Qed.
Hint Resolve zerop_nf_cb.
 
Definition redacc :
  list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> list (poly A0 eqA ltM).
intros H'; elim H'.
intros L; exact (nil (A:=poly A0 eqA ltM)).
intros a p Rec Acc.
apply
 LetP
  with
    (A := poly A0 eqA ltM)
    (h := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a (p ++ Acc)).
intros u H'0; case (zerop_dec A A0 eqA n ltM u); intros Z.
exact (Rec Acc).
exact (u :: Rec (u :: Acc)).
Defined.
 
Theorem redacc_cb :
 forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p (redacc L1 L2) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (L1 ++ L2).
intros L1; elim L1; auto.
simpl in |- *; auto.
intros L2 p H; elim H.
simpl in |- *; unfold LetP in |- *; intros a l H' L2 p.
case
 (zerop_dec A A0 eqA n ltM
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       a (l ++ L2))).
intros H'0 H'1.
apply Cb_incl with (P := l ++ L2) (1 := cs); auto.
simpl in |- *; auto.
simpl in |- *.
intros H'0 H'1; case H'1;
 [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; 
 auto.
apply Cb_cons; auto.
apply
 Cb_trans_cons
  with
    (p := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a (l ++ L2)); auto.
apply
 Cb_incl
  with
    (1 := cs)
    (P := l ++
          nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os a (l ++ L2) :: L2); auto.
change
  (incl
     (l ++
      nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
        a (l ++ L2) :: L2)
     (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
        a (l ++ L2) :: a :: l ++ L2)) in |- *.
apply incl_app; auto with datatypes.
apply Cb_cons; auto.
Qed.
 
Definition Red (L : list (poly A0 eqA ltM)) : list (poly A0 eqA ltM) :=
  redacc L nil.
 
Theorem Red_cb :
 forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p (Red L) -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
unfold Red in |- *.
intros L p H'.
generalize (redacc_cb L nil); simpl in |- *; auto.
rewrite <- app_nil_end; auto.
Qed.
 
Theorem cb_redacc :
 forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p L1 ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (redacc L1 L2 ++ L2).
intros L1; elim L1; simpl in |- *; auto.
intros L2 p H'; elim H'; auto.
unfold LetP in |- *.
intros a l H' L2 p H'0; case H'0;
 [ intros H'1; rewrite H'1; clear H'0 | intros H'1; clear H'0 ]; 
 auto.
case
 (zerop_dec A A0 eqA n ltM
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       p (l ++ L2))); auto.
intros H'0.
apply Cb_comp with (L1 := l ++ L2); auto.
intros p0 H'2.
lapply (in_app_or l L2 p0); auto.
intros H'3; case H'3; auto.
intros H'4; apply Cb_id with (1 := cs); auto with datatypes.
intros H'0.
2: case
    (zerop_dec A A0 eqA n ltM
       (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
          os a (l ++ L2))); auto.
2: intros H'0.
2: apply
    Cb_incl
     with
       (1 := cs)
       (P := redacc l
               (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
                  ltM_dec os a (l ++ L2) :: L2) ++
             nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a (l ++ L2) :: L2); auto with datatypes.
2: intros a0 H; case (in_app_or _ _ _ H); auto with datatypes.
2: simpl in |- *; intros H1; case H1; auto with datatypes.
apply
 Cb_compo
  with
    (L1 := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
             ltM_dec os p (l ++ L2) :: l ++ L2); simpl in |- *; 
 auto.
apply Cb_nf; auto.
intros q H'2; case H'2;
 [ intros H'3; rewrite <- H'3; clear H'2 | intros H'3; clear H'2 ];
 auto with datatypes.
apply Cb_id with (1 := cs); auto with datatypes.
case (in_app_or _ _ _ H'3); auto with datatypes.
intros H'2.
apply
 Cb_incl
  with
    (1 := cs)
    (P := redacc l
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os p (l ++ L2) :: L2) ++
          nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
            ltM_dec os p (l ++ L2) :: L2); auto with datatypes.
intros a0 H; case (in_app_or _ _ _ H); auto with datatypes.
simpl in |- *; intros H1; case H1; auto with datatypes.
intros H; apply Cb_id with (1 := cs); auto with datatypes.
Qed.
 
Theorem Cb_Red :
 forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p L -> Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (Red L).
intros L p H'.
lapply (cb_redacc L nil p); [ intros H'3; generalize H'3 | idtac ];
 simpl in |- *; auto.
rewrite <- app_nil_end; auto.
Qed.
 
Theorem cb_Red_cb1 :
 forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (Red L).
intros p L H'.
apply Cb_compo with (L1 := L); auto.
intros q H'0.
apply Cb_Red; auto.
Qed.
 
Theorem cb_Red_cb2 :
 forall (p : poly A0 eqA ltM) (L : list (poly A0 eqA ltM)),
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p (Red L) ->
 Cb A A0 eqA plusA multA eqA_dec n ltM ltM_dec p L.
intros p L H'.
apply Cb_compo with (L1 := Red L); auto.
intros q H'0.
apply Red_cb; auto.
Qed.
 
Theorem divp_id :
 forall p : poly A0 eqA ltM,
 ~ zerop A A0 eqA n ltM p -> divp A A0 eqA multA divA n ltM p p.
intros p; case p; auto.
intros x; case x; simpl in |- *; auto.
intros a l H' J.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a); [ intros Z | idtac ].
apply divTerm_def with (nZb := Z).
apply canonical_nzeroP with (p := l) (ltM := ltM); auto.
apply
 (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n)
  with (y := multTerm (A:=A) multA (n:=n) (T1 A1 n) a); 
 auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
apply canonical_nzeroP with (p := l) (ltM := ltM); auto.
Qed.
 
Theorem redacc_divp :
 forall (L1 L2 : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 ~ zerop A A0 eqA n ltM p ->
 In p (L1 ++ L2) ->
 exists q : poly A0 eqA ltM,
   In q (redacc L1 L2 ++ L2) /\
   divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros L1; elim L1; simpl in |- *; auto.
intros L2 p H' H'0; exists p; split; auto.
split; auto.
apply divp_id; auto.
unfold LetP in |- *.
intros a l H' L2 p H'0 H'1; case H'1;
 [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; 
 auto.
case
 (zerop_dec A A0 eqA n ltM
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       a (l ++ L2))); simpl in |- *; auto.
intros Z1.
lapply (nf_divp_zero a (l ++ L2));
 [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ];
 auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7;
 clear H'4 E H'6.
lapply (H' L2 q);
 [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ];
 auto.
case H'9; intros q0 E; case E; intros H'4 H'6; case H'6; intros H'8 H'10;
 clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := q); auto.
rewrite H'2; auto.
intros Z1.
lapply (nf_divp a (l ++ L2));
 [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ];
 auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7;
 clear H'4 E H'6.
simpl in H'3.
case H'3; [ intros H'4; clear H'3 | intros H'4; clear H'3 ].
exists q; split; [ idtac | split ]; auto.
lapply
 (H'
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       a (l ++ L2) :: L2) q);
 [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ];
 auto.
case H'9; intros q0 E; case E; intros H'3 H'6; case H'6; intros H'8 H'10;
 clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
case (in_app_or _ _ _ H'3); auto.
simpl in |- *; auto with datatypes.
simpl in |- *; intros H'6; case H'6;
 [ intros H'9; clear H'6 | intros H'9; clear H'6 ]; 
 auto.
auto with datatypes.
apply (divp_trans _ _ _ _ _ _ _ _ _ cs n ltM) with (y := q); auto.
case (in_app_or _ _ _ H'4); auto with datatypes.
rewrite H'2; auto.
case
 (zerop_dec A A0 eqA n ltM
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       a (l ++ L2))); simpl in |- *; auto.
intros Z1.
case (in_app_or _ _ _ H'2); auto.
intros H'3.
lapply
 (H'
    (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os
       a (l ++ L2) :: L2) p);
 [ intros H'6; lapply H'6; [ intros H'7; clear H'6 | clear H'6 ] | idtac ];
 auto with datatypes.
case H'7; intros q E; case E; intros H'4 H'5; case H'5; intros H'6 H'8;
 clear H'5 E H'7.
exists q; split; auto.
case (in_app_or _ _ _ H'4); auto with datatypes.
simpl in |- *; auto.
intros H; case H; intros H1; auto with datatypes.
intros H; exists p; split; [ right | idtac ]; auto with datatypes.
split; auto.
apply divp_id; auto.
Qed.
 
Theorem Red_divp :
 forall (L : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
 In p L ->
 ~ zerop A A0 eqA n ltM p ->
 exists q : poly A0 eqA ltM,
   In q (Red L) /\
   divp A A0 eqA multA divA n ltM p q /\ ~ zerop A A0 eqA n ltM q.
intros L p H' H'0.
lapply (redacc_divp L nil p); auto.
simpl in |- *; auto.
rewrite <- app_nil_end; auto.
rewrite <- app_nil_end; auto.
Qed.
 
Theorem Red_grobner :
 forall L : list (poly A0 eqA ltM),
 Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec L ->
 Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec
   (Red L).
intros L H'.
apply def_grobner; auto.
intros p H'0.
lapply (grobner_def L);
 [ intros H'2; lapply (H'2 p); [ intros H'4 | idtac ] | idtac ]; 
 auto.
case H'4; auto.
intros H'1; case H'1; intros q E; clear H'1.
right.
apply divp_reduce1 with (L1 := L) (q := q); auto.
intros r1 H'1 H'3.
lapply (Red_divp L r1);
 [ intros H'7; lapply H'7; [ intros H'8; clear H'7 | clear H'7 ] | idtac ];
 auto.
case H'8; intros q0 E0; case E0; intros H'5 H'6; case H'6; intros H'7 H'9;
 clear H'6 E0 H'8.
exists q0; split; auto.
apply cb_Red_cb2; auto.
Qed.
 
Definition redbuch (L : list (poly A0 eqA ltM)) : list (poly A0 eqA ltM) :=
  Red
    (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
       os L).
 
Theorem redbuch_stable :
 forall P : list (poly A0 eqA ltM),
 stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec P (redbuch P).
intros P.
cut
 (stable A A0 eqA plusA multA eqA_dec n ltM ltM_dec P
    (buch A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
       os P)).
intros H'0; inversion H'0; auto.
apply stable0; unfold redbuch in |- *; auto.
intros a H'.
apply cb_Red_cb1; auto.
intros a H'.
apply H0; auto.
apply cb_Red_cb2; auto.
apply buch_Stable; auto.
Qed.
 
Theorem redbuch_Grobner :
 forall P : list (poly A0 eqA ltM),
 Grobner A A0 A1 eqA plusA invA minusA multA divA eqA_dec n ltM ltM_dec
   (redbuch P).
intros P.
unfold redbuch in |- *.
apply Red_grobner; auto.
apply buch_Grobner; auto.
Qed.
End BuchRed.