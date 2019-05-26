(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : Application of Dickson lemma                           
                                                                           
          Henrik Persson
                                                                           
  ****************************************************************************)
Require Import List.
Require Import ListProps.
Require Import Bar.
Require Import Dickson.
Require Import Monomials.
Require Export BuchAux.
Section thRO.
Load "hCoefStructure".
Load "hOrderStructure".
Load "hBuchAux".
 
Definition get_mon : poly A0 eqA ltM -> mon n.
intros sp; case sp.
intros x H'; case x.
exact (M1 n).
intros a H'1; exact (T2M a).
Defined.
 
Theorem get_is_correct :
 forall (a b : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)),
 ~
 zerop A A0 eqA n ltM
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a
      P) ->
 In b P ->
 ~ zerop A A0 eqA n ltM b ->
 ~
 mdiv n (get_mon b)
   (get_mon
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os a P)).
intros a b P H' H'0 H'1.
cut
 (irreducible A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P
    (s2p A A0 eqA n ltM
       (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
          os a P))).
2: try exact (nf_irreducible a P); auto.
generalize H';
 case
  (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a
     P); simpl in |- *; auto.
intros x; case x; simpl in |- *.
intros H'2 H'3; elim H'3; auto.
intros a0 l H'2 H'3 H'4; red in |- *; intros H'5; red in H'4.
red in H'4.
generalize H'0 H'1 H'5; case b.
intros x0; case x0; simpl in |- *.
intros o H'6 H'7; elim H'7; auto.
intros a1 l0 o H'6 H'7 H'8.
cut (~ zeroP (A:=A) A0 eqA (n:=n) a1); [ intros nZa1 | idtac ].
apply 
 H'4
   with
     (q := spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec
             a0 a1 nZa1 l l0); auto.
change
  (reduce A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec P
     (pX a0 l)
     (spminusf A A0 A1 eqA invA minusA multA divA eqA_dec n ltM ltM_dec a0 a1
        nZa1 l l0)) in |- *.
apply reducetop_sp with (1 := cs) (b := a1) (nZb := nZa1) (q := l0); auto.
change
  (inPolySet A A0 eqA n ltM
     (s2p A A0 eqA n ltM (mks A A0 eqA n ltM (pX a1 l0) o)) P) 
 in |- *.
apply in_inPolySet; auto.
simpl in |- *; auto.
red in |- *; intros H'9; inversion H'9.
apply divTerm_def with (nZb := nZa1); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
apply divTerm_on_plusM_minusM with (1 := cs); auto.
apply canonical_nzeroP with (ltM := ltM) (p := l); auto.
simpl in |- *; auto.
apply sym_equal; auto.
apply mdiv_div; auto.
apply canonical_nzeroP with (ltM := ltM) (p := l0); auto.
apply nf_irreducible; auto.
Qed.
 
Definition get_monL : list (poly A0 eqA ltM) -> list (mon n) := map get_mon.
 
Inductive RO : list (poly A0 eqA ltM) -> list (poly A0 eqA ltM) -> Prop :=
    RO0 :
      forall (a : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)),
      ~
      zerop A A0 eqA n ltM
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a P) ->
      RO
        (P ++
         nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a P :: nil) P.
 
Definition BadM (l : list (mon n)) := GoodR (mon n) (mdiv n) l -> False.
 
Lemma l1 :
 forall (cs : list (poly A0 eqA ltM)) (ms : list (mon n)),
 Bar (mon n) (GoodR (mon n) (mdiv n)) ms ->
 forall bs : list (poly A0 eqA ltM),
 ms = get_monL bs ->
 (forall f : poly A0 eqA ltM, In f bs -> ~ zerop A A0 eqA n ltM f) ->
 BadM ms -> Acc RO (cs ++ rev bs).
intros cs1 ms1 H; elim H; auto.
intros l H' bs H'0 H'1 H'2.
case H'2; auto.
intros l H' H'0 bs Heq Hnz H'1; auto.
apply Acc_intro; auto.
intros y H'2; inversion H'2; auto.
rewrite <- ass_app.
change
  (Acc RO
     (cs1 ++
      rev bs ++
      rev
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a (cs1 ++ rev bs) :: nil))) in |- *.
rewrite <- distr_rev; simpl in |- *.
change
  (Acc RO
     (cs1 ++
      rev
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a (cs1 ++ rev bs) :: bs))) in |- *.
apply
 H'0
  with
    (a := get_mon
            (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
               ltM_dec os a (cs1 ++ rev bs))); unfold get_monL in |- *;
 try rewrite Heq; simpl in |- *; auto.
intros f H'3; elim H'3;
 [ intros H'4; rewrite <- H'4; clear H'3 | intros H'4; clear H'3 ]; 
 auto.
apply tdivGoodP with (trm := mon n) (tdiv := mdiv n); auto.
rewrite <- Heq; auto.
intros g.
intros H'3; cut (ex (fun b : poly A0 eqA ltM => g = get_mon b /\ In b bs)).
intros H'4; elim H'4; intros b E; elim E; intros H'5 H'6; rewrite H'5;
 clear E H'4; auto.
apply get_is_correct; auto.
apply in_or_app; apply or_intror; apply in_rev; auto.
apply map_in; auto.
Qed.
 
Theorem wf_incl : well_founded RO.
unfold well_founded in |- *; intros.
apply Acc_intro; intros.
inversion H.
apply
 l1
  with
    (bs := nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
             ltM_dec os a0 a :: nil)
    (ms := get_monL
             (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM
                ltM_dec os a0 a :: nil)); auto.
change
  (GRBar (mon n) (mdiv n)
     (get_mon
        (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
           os a0 a) :: nil)) in |- *.
apply nilGRBar; auto.
apply dicksonL with (n := n); auto.
simpl in |- *; intros f H3; case H3; intros.
rewrite <- H4; auto.
elim H4.
red in |- *; intros H4; inversion H4; inversion H5.
Qed.
 
Lemma RO_lem :
 forall (a : poly A0 eqA ltM) (P : list (poly A0 eqA ltM)),
 ~
 zerop A A0 eqA n ltM
   (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec os a
      P) ->
 RO
   (addEnd A A0 eqA n ltM
      (nf A A0 A1 eqA plusA invA minusA multA divA cs eqA_dec n ltM ltM_dec
         os a P) P) P.
intros a P H'; rewrite addEnd_app.
apply RO0; auto.
Qed.
End thRO.