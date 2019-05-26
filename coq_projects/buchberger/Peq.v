(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : equality over polynomials                       
                                                                           
          Laurent Thery March 97 (revised April 01)                          
                                                                           
  ***************************************************************************
   definition of Peq *)

Require Export Relation_Definitions.
Require Import Arith.
Require Import Compare_dec.
Require Export CoefStructure.
Require Export OrderStructure.
Require Export POrder.
Require Export Monomials.
Require Export Term.
Require Export List.
Section Peq.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hOrder".
 
Definition size := length (A:=Term A n).
 
Definition sizel m := match m with
                      | (l1, l2) => size l1 + size l2
                      end.
 
Definition lessP m1 m2 := sizel m1 < sizel m2.
Hint Unfold lessP.
 
Lemma wf_lessP : well_founded lessP.
red in |- *.
cut (forall (m : nat) a, sizel a < m -> Acc lessP a).
intros H' a.
apply H' with (m := S (sizel a)); auto.
intros m; elim m; clear m.
intros a H; inversion H.
intros m H' a H'0.
apply Acc_intro.
intros y H'1; apply H'.
unfold lessP in H'1.
apply lt_le_trans with (sizel a); auto with arith.
Qed.
Hint Resolve wf_lessP.
 
Theorem pX_inj :
 forall (n1 n2 : Term A n) l1 l2, n1 = n2 -> l1 = l2 -> pX n1 l1 = pX n2 l2.
intros n1 n2 l1 l2 H' H'0; rewrite H'0; rewrite H'; auto.
Qed.
Hint Resolve pX_inj.
 
Lemma pX_invl : forall (a b : Term A n) p q, pX a p = pX b q -> a = b.
intros a b p q H'; inversion H'; auto.
Qed.
Hint Unfold pX.
 
Lemma pX_invr : forall p q (a b : Term A n), pX a p = pX b q -> p = q.
unfold pX, pX in |- *.
intros p q a b H'; inversion H'; auto.
Qed.
 
Theorem canonicalpO : canonical A0 eqA ltM (pO A n).
split; auto.
apply olistO.
red in |- *; simpl in |- *; auto.
Qed.
 
Theorem canonicalp1 :
 forall a,
 ~ zeroP (A:=A) A0 eqA (n:=n) a -> canonical A0 eqA ltM (pX a (pO A n)).
intros a H; split; simpl in |- *; auto.
red in |- *; simpl in |- *; apply Relation_Operators_compat.d_one.
Qed.
Hint Resolve canonicalp1 canonical0.
 
Inductive eqP : list (Term A n) -> list (Term A n) -> Prop :=
  | eqP0 : eqP (pO A n) (pO A n)
  | eqpP1 :
      forall ma mb p q,
      eqTerm (A:=A) eqA (n:=n) ma mb -> eqP p q -> eqP (pX ma p) (pX mb q).
Hint Resolve eqP0 eqpP1.
 
Theorem eqp_refl : reflexive _ eqP.
red in |- *.
intros x; elim x; auto.
intros a l H; change (eqP (pX a l) (pX a l)) in |- *; apply eqpP1; auto.
Qed.
 
Theorem eqp_sym : symmetric _ eqP.
red in |- *.
intros x y H'; elim H'; auto.
intros ma mb p q H H0 H1.
apply eqpP1; auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); auto.
Qed.
 
Lemma eqp_inv1 : forall p, eqP (pO A n) p -> p = pO A n.
unfold pO in |- *; intros p H'; inversion H'; auto.
Qed.
 
Theorem eqp_inv2 : forall p, eqP p (pO A n) -> p = pO A n.
unfold pO in |- *; intros p H'; inversion H'; auto.
Qed.
 
Theorem eqp_inv3l :
 forall a b p q, eqP (pX a p) (pX b q) -> eqTerm (A:=A) eqA (n:=n) a b.
intros a b p q H'; simple inversion H'; auto.
unfold pO in H0; inversion H0.
rewrite (pX_invl ma a p0 p); auto; rewrite (pX_invl mb b q0 q); auto.
Qed.
 
Theorem eqp_inv3r : forall a b p q, eqP (pX a p) (pX b q) -> eqP p q.
intros a b p q H'; simple inversion H'; auto.
unfold pO in H0; inversion H0.
rewrite (pX_invr p0 p ma a); auto; rewrite (pX_invr q0 q mb b); auto.
Qed.
 
Theorem eqp_trans : transitive _ eqP.
red in |- *.
intros x; elim x; auto.
intros y z H'; inversion_clear H'.
intros H'0; inversion_clear H'0; auto.
intros a l H' y z H'0; inversion_clear H'0.
intros H4; inversion_clear H4.
change (eqP (pX a l) (pX mb0 q0)) in |- *; apply eqpP1; eauto.
apply (eqTerm_trans _ _ _ _ _ _ _ _ _ cs n) with (y := mb); auto.
Qed.
Hint Resolve eqp_refl.
 
Let eqTerm_imp_eqT := eqTerm_imp_eqT A eqA n.
 
Theorem ltP_refl_pX :
 forall (a : Term A n) (p : list (Term A n)),
 canonical A0 eqA ltM (pX a p) -> ltP (A:=A) (n:=n) ltM p (pX a p).
intros a p; case p; auto.
intros a0 l H'.
apply ltP_trans with (y := pX a (pO A n)); auto.
change (ltP (A:=A) (n:=n) ltM (pX a0 l) (pX a (pO A n))) in |- *.
apply ltP_hd; auto.
apply (canonical_pX_order A A0) with (eqA := eqA) (l := l); auto.
apply ltP_tl; auto.
change (ltP (A:=A) (n:=n) ltM (pO A n) (pX a0 l)) in |- *; apply ltPO.
Qed.
 
Theorem eqp_eqTerm :
 forall a b p q, eqP (pX a p) (pX b q) -> eqTerm (A:=A) eqA (n:=n) a b.
intros a b p q H'; inversion_clear H'; trivial.
Qed.
 
Theorem ltp_eqp_comp :
 forall p q r s,
 ltP (A:=A) (n:=n) ltM p q ->
 canonical A0 eqA ltM p ->
 canonical A0 eqA ltM q -> eqP p r -> eqP q s -> ltP (A:=A) (n:=n) ltM r s.
intros p q r s H'; generalize r s; elim H'; clear r s H'; auto.
intros x p0 r s H H0 H1; inversion H1.
intros H4; inversion H4; apply ltPO.
intros x y p0 q0 H r s H0 H1 H2 H3; inversion_clear H2; try discriminate;
 inversion_clear H3; try discriminate; auto.
apply ltP_hd.
apply ltT_eqTl with (a := y); auto.
apply ltT_eqTr with (a := x); auto.
intros x y p0 q0 H H0 H1 r s H2 H3 H4 H5; inversion_clear H4;
 try discriminate; inversion_clear H5; try discriminate.
apply ltP_tl; auto.
apply (eqT_trans A n) with (y := y); auto.
apply (eqT_trans A n) with (y := x); auto.
apply (eqT_sym A n); auto.
apply H1; auto.
apply canonical_imp_canonical with (a := x); auto.
apply canonical_imp_canonical with (a := y); auto.
Qed.
 
Theorem eqp_imp_canonical :
 forall p q, eqP p q -> canonical A0 eqA ltM p -> canonical A0 eqA ltM q.
intros p q H'; elim H'; auto.
intros ma mb p0 q0 H'0 H'1 H'2 H'3.
apply canonical_pX_eqT with (a := ma); auto.
apply ltP_pX_canonical; auto.
apply H'2.
apply canonical_imp_canonical with (a := ma); auto.
apply (canonical_nzeroP A A0 eqA n ltM ma p0); auto.
apply ltp_eqp_comp with (p := p0) (q := pX ma (pO A n)); auto.
apply canonical_pX_ltP with (1 := H'3).
apply canonical_imp_canonical with (a := ma); auto.
apply canonicalp1; auto.
apply (canonical_nzeroP A A0 eqA n ltM ma p0); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := ma); auto.
apply (canonical_nzeroP A A0 eqA n ltM ma p0); auto.
Qed.
 
Definition sizel3
  (m : list (Term A n) * (list (Term A n) * list (Term A n))) :=
  match m with
  | (l1, (l2, l3)) => size l1 + (size l2 + size l3)
  end.
 
Definition lessP3
  (m1 m2 : list (Term A n) * (list (Term A n) * list (Term A n))) :=
  sizel3 m1 < sizel3 m2.
 
Lemma wf_lessP3 : well_founded lessP3.
red in |- *.
cut (forall (m : nat) a, sizel3 a < m -> Acc lessP3 a).
intros H' a.
apply H' with (m := S (sizel3 a)); auto.
intros m; elim m; clear m.
intros a H; inversion H.
intros p H' a H'0; apply Acc_intro.
intros y H'1; apply H'.
unfold lessP in H'1; apply lt_le_trans with (sizel3 a); auto with arith.
Qed.
Hint Resolve wf_lessP3.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition eqPf :
  forall pq, {eqP (fst pq) (snd pq)} + {~ eqP (fst pq) (snd pq)}.
intros pq; pattern pq in |- *;
 apply well_founded_induction with (R := lessP) (1 := wf_lessP); 
 clear pq.
intros pq; case pq; simpl in |- *; clear pq.
intros p; case p; clear p.
intros q; case q; clear q.
intros H'; left; constructor.
intros b q H'; right; red in |- *; intros H'0; inversion H'0.
intros a p q; case q; clear q.
intros H'; right; red in |- *; intros H'0; inversion H'0.
intros b q Rec; case (eqTerm_dec _ _ eqA_dec n a b); simpl in Rec;
 intros eqTerm0.
case (Rec (p, q)); unfold lessP in |- *; simpl in |- *; auto with arith.
intros H'; left; auto.
change (eqP (pX a p) (pX b q)) in |- *; auto.
intros H'; right; red in |- *; intros H'0.
apply H'.
apply eqp_inv3r with (a := a) (b := b); auto.
right; red in |- *; intros H'.
apply eqTerm0.
apply eqp_eqTerm with (p := p) (q := q); auto.
Defined.
 
Definition seqP : poly A0 eqA ltM -> poly A0 eqA ltM -> Prop.
intros sp1 sp2; case sp1; case sp2.
intros p1 H'1 p2 H'2; exact (eqP p1 p2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem seqp_dec : forall p q : poly A0 eqA ltM, {seqP p q} + {~ seqP p q}.
intros p q; case p; case q; simpl in |- *.
intros x H' x0 H'0.
apply (eqPf (x, x0)).
Qed.
 
Theorem seqp_refl : reflexive (poly A0 eqA ltM) seqP.
red in |- *.
intros p; case p; simpl in |- *.
intros x H'.
apply eqp_refl.
Qed.
 
Theorem seqp_sym : symmetric (poly A0 eqA ltM) seqP.
red in |- *.
intros p q; case p; case q; simpl in |- *.
intros x H' x0 H'0 H'1.
apply eqp_sym; auto.
Qed.
 
Theorem seqp_trans : transitive (poly A0 eqA ltM) seqP.
red in |- *.
intros p q r; case p; case q; case r; simpl in |- *.
intros x H' x0 H'0 x1 H'1 H'2 H'3.
apply eqp_trans with (y := x0); auto.
Qed.
End Peq.