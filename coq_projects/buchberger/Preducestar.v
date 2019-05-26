(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : reduction  star                                         
                                                                           
          Laurent Thery May 97 (revised April 01)                            
                                                                           
  ****************************************************************************)
Require Export Preduceplus.
Unset Standard Proposition Elimination Names.
Section Preducestar.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hReduceplus".
 
Inductive reducestar (Q : list (poly A0 eqA ltM)) :
list (Term A n) -> list (Term A n) -> Prop :=
    reducestar0 :
      forall p q : list (Term A n),
      reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p
        q ->
      irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
        q -> reducestar Q p q.
 
Theorem reducestar_eqp_com :
 forall (Q : list (poly A0 eqA ltM)) (p q r s : list (Term A n)),
 reducestar Q p q ->
 canonical A0 eqA ltM p ->
 eqP A eqA n p r -> eqP A eqA n q s -> reducestar Q r s.
intros Q p q r s H' H'0 H'1 H'2; inversion H'.
apply reducestar0; auto.
apply reduceplus_eqp_com with (p := p) (q := q) (1 := cs); auto.
apply irreducible_eqp_com with (p := q) (1 := cs); auto.
apply canonical_reduceplus with (1 := cs) (3 := H); auto.
Qed.
 
Definition mks :
  forall p : list (Term A n), canonical A0 eqA ltM p -> poly A0 eqA ltM.
intros p H'; exists p; exact H'.
Defined.
 
Definition selectdivf :
  forall a : Term A n,
  ~ zeroP (A:=A) A0 eqA (n:=n) a ->
  forall Q : list (poly A0 eqA ltM),
  {q : list (Term A n) |
  exists b : Term A n,
    (exists p : list (Term A n),
       divP A A0 eqA multA divA n a b /\
       inPolySet A A0 eqA n ltM q Q /\ q = pX b p)} +
  {(forall (b : Term A n) (q : list (Term A n)),
    inPolySet A A0 eqA n ltM (pX b q) Q -> ~ divP A A0 eqA multA divA n a b)}.
intros a Z Q; elim Q; auto.
right.
intros b q H'; inversion_clear H'.
intros a0; case a0.
intros x; case x.
intros c l H'; case H'.
intros H'1; case H'1.
intros x0 H'0; left.
exists x0.
elim H'0; intros b E; elim E; intros p E0; elim E0; intros H'2 H'3; elim H'3;
 intros H'4 H'5; try exact H'5; clear H'3 E0 E H'0.
exists b; exists p; split; [ idtac | split ]; auto.
apply inskip; auto.
intros H'0; right.
intros b q H'1; inversion_clear H'1; auto.
apply H'0 with (q := q); auto.
intros a1 l c l0 H'; case (divP_dec _ _ _ _ _ _ _ _ _ cs n a a1); auto.
apply canonical_nzeroP with (p := l) (ltM := ltM); auto.
intros divP1; left; exists (pX a1 l); auto.
exists a1; exists l; split; [ idtac | split ]; auto.
change
  (inPolySet A A0 eqA n ltM (pX a1 l)
     (exist (canonical A0 eqA ltM) (pX a1 l) c :: l0)) 
 in |- *.
apply incons with (a := a1) (p := l) (H := c); auto.
intros divP1; case H'; intros Hyp1.
case Hyp1.
intros x0 H'0; left; exists x0.
elim H'0; intros b E; elim E; intros p E0; elim E0; intros H'1 H'2; elim H'2;
 intros H'3 H'4; try exact H'4; clear H'2 E0 E H'0.
exists b; exists p; split; [ idtac | split ]; auto.
apply inskip; auto.
right.
intros b q H'1; generalize divP1; inversion_clear H'1; eauto.
Qed.
 
Definition selectpolyf :
  forall (Q : list (poly A0 eqA ltM)) (r : list (Term A n)),
  canonical A0 eqA ltM r ->
  {q : list (Term A n) |
  reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q r q} +
  {irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q r}.
intros Q r; elim r.
intros H'; right;
 change
   (irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
      (pO A n)) in |- *; apply pO_irreducible; auto.
intros a l H' H'0.
cut (canonical A0 eqA ltM l);
 [ intros C0 | apply canonical_imp_canonical with (a := a); auto ].
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (p := l) (ltM := ltM); auto ].
case (selectdivf a Z0 Q); intros Hyp1.
case Hyp1.
intros x0; case x0; left.
absurd True; auto.
elim e; intros b E; elim E; intros p E0; elim E0; intros H'1 H'2; elim H'2;
 intros H'3 H'4; inversion H'4; clear H'2 E0 E e.
cut (~ zeroP (A:=A) A0 eqA (n:=n) t); [ intros nZt | idtac ].
exists
 (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a t nZt l
    l0).
elim e; intros b E; elim E; intros p E0; elim E0; intros H'1 H'2; elim H'2;
 intros H'3 H'4; clear H'2 E0 E e.
change
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
     (pX a l)
     (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a t
        nZt l l0)) in |- *.
apply reducetop_sp with (1 := cs); auto.
rewrite (pX_invl A n t b l0 p); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l0).
apply inPolySet_imp_canonical with (L := Q); auto.
elim e; intros b E; elim E; intros p E0; elim E0; intros H'1 H'2; elim H'2;
 intros H'3 H'4; try exact H'3; clear H'2 E0 E e.
lapply H'; [ intros H'1; case H'1; clear H' | clear H' ].
intros H'; case H'.
intros x H'2; left; exists (pX a x).
change
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
     (pX a l) (pX a x)) in |- *.
apply reduceskip; auto.
intros H'; right;
 change
   (forall q : list (Term A n),
    ~
    reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
      (pX a l) q) in |- *.
intros q; red in |- *; intros H'2; generalize H' Hyp1; inversion_clear H'2.
intros H'3 H'4; lapply (H'4 b q0); [ intros H'7; apply H'7 | idtac ]; auto.
intros H'3 H'4;
 absurd
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q l q0);
 auto.
auto.
Qed.
 
Definition Reducef :
  forall (Q : list (poly A0 eqA ltM)) (p : poly A0 eqA ltM),
  {q : poly A0 eqA ltM |
  reducestar Q (s2p A A0 eqA n ltM p) (s2p A A0 eqA n ltM q)}.
intros Q p; pattern p in |- *.
apply well_founded_induction with (1 := sltp_wf _ A0 eqA _ ltM os).
intros x; case x.
intros x0; case x0.
intros o H'; simpl in |- *.
exists (mks (pO A n) (canonicalpO A A0 eqA n ltM)); simpl in |- *; auto.
apply reducestar0; auto.
apply Rstar_0; auto.
apply pO_irreducible; auto.
simpl in |- *; intros a l o H'; auto.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a);
 [ intros Z0 | apply canonical_nzeroP with (ltM := ltM) (p := l) ]; 
 auto.
lapply (selectdivf a);
 [ intros H'1; case (H'1 Q) | idtac ];
 auto; intros Div1.
case Div1.
intros x1; case x1.
intros H'0; absurd True; auto.
elim H'0; intros b E; elim E; intros p0 E0; elim E0; intros H'3 H'4; elim H'4;
 intros H'5 H'6; inversion_clear H'6; clear H'4 E0 E H'0.
intros a0 l0 H'0.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a0); [ intros nZt | idtac ].
2: apply canonical_nzeroP with (p := l0) (ltM := ltM).
2: apply inPolySet_imp_canonical with (L := Q); auto.
2: elim H'0; intros b E; elim E; intros p0 E0; elim E0; intros H'3 H'4;
    elim H'4; intros H'5 H'6; try exact H'5; clear H'4 E0 E H'0.
cut
 (canonical A0 eqA ltM
    (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0
       nZt l l0)); [ intros Op2 | idtac ]; auto.
lapply
 (H'
    (mks
       (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
          a0 nZt l l0) Op2)); [ intros H'4; case H'4 | idtac ]; 
 auto.
intros x2 H'3; exists x2.
apply reducestar0; auto.
apply
 Rstar_n
  with
    (y := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a
            a0 nZt l l0); auto.
elim H'0; intros b E; elim E; intros p0 E0; elim E0; intros H'5 H'6; elim H'6;
 intros H'7 H'8; clear H'6 E0 E H'0.
change
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
     (pX a l)
     (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0
        nZt l l0)) in |- *.
apply reducetop_sp with (1 := cs); auto.
rewrite (pX_invl A n a0 b l0 p0); auto.
inversion_clear H'3; auto.
inversion_clear H'3; auto.
simpl in |- *;
 apply
  ltP_reduce
   with (Q := Q) (eqA_dec := eqA_dec) (ltM_dec := ltM_dec) (1 := cs); 
 auto.
elim H'0; intros b E; elim E; intros p0 E0; elim E0; intros H'3 H'4; elim H'4;
 intros H'5 H'6; clear H'4 E0 E H'0.
change
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q 
     (pX a l)
     (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a a0
        nZt l l0)) in |- *.
apply reducetop_sp with (1 := cs); auto.
rewrite (pX_invl A n a0 b l0 p0); auto.
apply canonical_spminusf with (1 := cs); auto.
apply canonical_imp_canonical with (a := a); auto.
elim H'0; intros b E; elim E; intros p0 E0; elim E0; intros H'3 H'4; elim H'4;
 intros H'5 H'6; clear H'4 E0 E H'0.
apply canonical_imp_canonical with (a := a0); auto.
apply inPolySet_imp_canonical with (L := Q); auto.
elim H'0; intros b E; elim E; intros p0 E0; elim E0; intros H'3 H'4; elim H'4;
 intros H'5 H'6; clear H'4 E0 E H'0.
rewrite (pX_invl A n a0 b l0 p0); auto.
cut (canonical A0 eqA ltM l);
 [ intros Op2 | apply canonical_imp_canonical with (a := a); auto ].
lapply (H' (mks l Op2)); simpl in |- *; [ intros H'3; case H'3 | idtac ];
 auto.
2: change (ltP (A:=A) (n:=n) ltM l (pX a l)) in |- *;
    apply ltP_refl_pX with (1 := cs); auto.
intros x1; case x1.
intros x2 c H'4; simpl in |- *; cut (canonical A0 eqA ltM (pX a x2));
 [ intros Op3 | auto ].
exists (mks (pX a x2) Op3); simpl in |- *.
apply reducestar0; auto.
change
  (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
     (pX a l) (pX a x2)) in |- *.
apply reduceplus_skip with (1 := cs); auto.
inversion_clear H'4; auto.
change
  (forall p : list (Term A n),
   ~
   reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
     (pX a x2) p) in |- *.
intros p0; red in |- *; intros H'5; generalize H'4 Div1; inversion_clear H'5;
 simpl in |- *.
intros H'6 H'7; lapply (H'7 b q); [ intros H'10; apply H'10 | idtac ]; auto.
intros H'6 H'7;
 absurd
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x2 q);
 auto.
inversion_clear H'6; auto.
cut
 (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (pX a l) (pX a x2)); [ intros Re0 | idtac ].
apply canonical_reduceplus with (1 := cs) (3 := Re0); auto.
apply reduceplus_skip with (1 := cs); auto.
inversion_clear H'4; auto.
Defined.
 
Theorem reduce0_reducestar :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 canonical A0 eqA ltM p -> exists t : list (Term A n), reducestar Q p t.
intros Q p H.
generalize (Reducef Q (mks p H)).
intros H'; elim H'.
simpl in |- *.
intros x H'0; exists (s2p A A0 eqA n ltM x); try assumption.
Qed.
 
Theorem reducestar_trans :
 forall (Q : list (poly A0 eqA ltM)) (x y z : list (Term A n)),
 canonical A0 eqA ltM x ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q x y ->
 reducestar Q y z -> reducestar Q x z.
intros Q x y z H' H'0 H'1; inversion H'1.
apply reducestar0; auto.
apply reduceplus_trans with (1 := cs) (y := y); auto.
Qed.
 
Theorem reducestar_reduceplus :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reducestar Q p q ->
 reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p q.
intros Q p q H'; inversion H'; auto.
Qed.
 
Theorem reducestar_irreducible :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reducestar Q p q ->
 irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q q.
intros Q p q H'; inversion H'; auto.
Qed.
Hint Resolve reducestar_reduceplus.
 
Theorem reducestar_inv :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 reducestar Q p q ->
 canonical A0 eqA ltM p ->
 eqP A eqA n p q /\
 irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p \/
 (exists r : list (Term A n),
    reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q p r /\
    reducestar Q r q).
intros Q p q H'; elim H'.
intros p0 q0 H'0; inversion H'0.
intros H'1 H'2; left; split; auto.
apply irreducible_eqp_com with (1 := cs) (p := q0); auto.
apply eqp_imp_canonical with (p := p0) (1 := cs); auto.
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); auto.
intros H'1 H'2; right; exists y; split; auto.
apply reducestar0; auto.
Qed.
 
Lemma pO_reducestar :
 forall (Q : list (poly A0 eqA ltM)) (p : list (Term A n)),
 reducestar Q (pO A n) p -> p = pO A n.
intros Q p H'.
cut
 (reduceplus A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec Q
    (pO A n) p); [ intros Red1 | apply reducestar_reduceplus; auto ].
apply pO_reduceplus with (2 := Red1); auto.
Qed.
 
Theorem reducestar_pO_is_pO :
 forall (Q : list (poly A0 eqA ltM)) (p q : list (Term A n)),
 canonical A0 eqA ltM p -> reducestar Q (pO A n) (pO A n).
intros Q p H' H'0; auto.
apply reducestar0; auto.
apply Rstar_0; auto.
apply pO_irreducible.
Qed.
 
Theorem reducestar_in_pO :
 forall (Q : list (poly A0 eqA ltM)) (a : Term A n) (p : list (Term A n)),
 inPolySet A A0 eqA n ltM p Q ->
 ~ zeroP (A:=A) A0 eqA (n:=n) a ->
 reducestar Q (mults (A:=A) multA (n:=n) a p) (pO A n).
intros Q a p H' H'0.
cut (canonical A0 eqA ltM p); [ intros Op0 | idtac ].
apply
 reducestar_eqp_com
  with
    (p := mults (A:=A) multA (n:=n) a p)
    (q := mults (A:=A) multA (n:=n) a (pO A n)); auto.
apply reducestar0; auto.
apply reduceplus_mults with (1 := cs); auto.
apply reduce_imp_reduceplus with (1 := cs); auto.
apply reduce_in_pO with (1 := cs); auto.
simpl in |- *; apply pO_irreducible; auto.
apply inPolySet_imp_canonical with (L := Q); auto.
Qed.
 
Definition pickinSet :
  forall a : Term A n,
  ~ zeroP (A:=A) A0 eqA (n:=n) a ->
  forall Q : list (poly A0 eqA ltM),
  {p : list (Term A n) | pickinSetp A A0 eqA multA divA n ltM a p Q} +
  {(forall (b : Term A n) (p q : list (Term A n)),
    inPolySet A A0 eqA n ltM p Q ->
    divP A A0 eqA multA divA n a b -> p <> pX b q)}.
intros a Z0 Q; elim Q.
right; intros b p q H'; inversion_clear H'.
intros a0; case a0.
intros x; case x.
intros c l H'; case H'; auto.
intros H'0; left; inversion_clear H'0.
exists x0; auto.
apply pickinSetskip; auto.
intros H'0; right.
intros b p q H'1; inversion_clear H'1.
intros H'3; red in |- *; intros H'4.
lapply (H'0 b p q);
 [ intros H'7; lapply H'7; [ intros H'8; clear H'7 | clear H'7 ] | idtac ];
 auto.
intros a1 l c l0 H'.
case divP_dec with (1 := cs) (a := a) (b := a1); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
intros H'0; left; exists (pX a1 l); auto.
change
  (pickinSetp A A0 eqA multA divA n ltM a (pX a1 l) (mks (pX a1 l) c :: l0))
 in |- *; unfold mks in |- *; auto.
apply (pickinSeteqp A A0 eqA multA divA n ltM); auto.
intros Hyp.
case H'; intros H'1.
inversion H'1.
left; exists x0; auto.
apply pickinSetskip; auto.
right.
intros b p q H'2; inversion_clear H'2; auto.
intros H'3; red in |- *; intros H'4; apply Hyp.
injection H'4.
intros H'5 H'6; rewrite H'6; auto.
Defined.
End Preducestar.
