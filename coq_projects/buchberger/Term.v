(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

(****************************************************************************
                                                                           
          Buchberger : Terms                           
                                                                           
          Laurent Thery April 01                          
                                                                           
  ****************************************************************************)
Require Import Relation_Definitions.
Require Import CoefStructure.
Require Import moreCoefStructure.
Require Import OrderStructure.
Require Import Monomials.
Section Term.
Load "hCoefStructure".
Load "mCoefStructure".
Load "hOrderStructure".
Load "mOrderStructure".
 
Definition M1 := zero_mon n.
 
Definition Term := (A * mon n)%type.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition zeroP : Term -> Prop.
intros H'; case H'.
intros a H'1; exact (eqA a A0).
Defined.
 
Definition eqTerm : Term -> Term -> Prop.
intros H'; case H'.
intros a a' H'2; case H'2.
intros b b'; exact (eqA a b /\ a' = b').
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem eqTerm_refl : reflexive Term eqTerm.
red in |- *.
intros x; case x; simpl in |- *; auto.
Qed.
 
Theorem eqTerm_sym : symmetric Term eqTerm.
red in |- *.
intros x y; case x; case y; simpl in |- *; intuition.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.
 
Theorem eqTerm_trans : transitive Term eqTerm.
red in |- *.
intros x y z; case x; case y; case z; simpl in |- *; intuition.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := a0); auto.
rewrite H2; auto.
Qed.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition T2M : Term -> mon n.
intros t; case t; intros a m; exact m.
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition eqT (a b : Term) : Prop := T2M a = T2M b.
Hint Unfold eqT.
Set Strict Implicit.
Unset Implicit Arguments.
 
Lemma eqT_refl : reflexive _ eqT.
red in |- *; auto.
Qed.
 
Lemma eqT_sym : symmetric _ eqT.
red in |- *; auto.
Qed.
 
Lemma eqT_trans : transitive _ eqT.
red in |- *; unfold eqT in |- *.
intros x y z H' H'0; rewrite H'; auto.
Qed.
 
Theorem eqTerm_imp_eqT : forall a b : Term, eqTerm a b -> eqT a b.
intros a b; case a; case b; simpl in |- *; intuition.
Qed.
 
Theorem eqTerm_dec : forall x y : Term, {eqTerm x y} + {~ eqTerm x y}.
intros x y; case x; case y; simpl in |- *.
intros b2 c2 b3 c3.
case (eqA_dec b3 b2); intros eqAZ; auto.
case (eqmon_dec n c3 c2); intros eqAZ1; auto.
right; red in |- *; intros H'; elim H'; intros H'0 H'1; clear H'; auto.
right; red in |- *; intros H'; elim H'; intros H'0 H'1; clear H'; auto.
Qed.
 
Theorem eqT_zerop_is_eqTerm :
 forall a b : Term, eqT a b -> zeroP a -> zeroP b -> eqTerm a b.
intros a b; case a; case b; simpl in |- *; auto.
intuition.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := A0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.
 
Theorem zeroP_dec : forall x : Term, {zeroP x} + {~ zeroP x}.
intros x; case x; simpl in |- *.
intros b H'.
apply eqA_dec; auto.
Qed.
 
Theorem zeroP_comp_eqTerm :
 forall a b : Term, zeroP a -> eqTerm a b -> zeroP b.
intros a b; case a; case b; simpl in |- *; auto.
intuition.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := a1); auto;
 apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.

Theorem nzeroP_comp_eqTerm :
 forall a b : Term, ~ zeroP a -> eqTerm a b -> ~ zeroP b.
intros a b H' H'0; red in |- *; intros H'1.
apply H'.
apply zeroP_comp_eqTerm with (a := b); auto.
apply eqTerm_sym; auto.
Qed.


Set Implicit Arguments.
Unset Strict Implicit.
 
Definition plusTerm : Term -> Term -> Term.
intros x; case x; intros b2 c2; intros y; case y; intros b3 c3;
 exact (plusA b2 b3, c2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem zeroP_plusTermr :
 forall a b : Term, eqT a b -> zeroP b -> eqTerm a (plusTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 m1 a2 m2 H1 H2; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA a2 A0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.
 
Theorem zeroP_plusTerml :
 forall a b : Term, eqT a b -> zeroP a -> eqTerm b (plusTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 m1 a2 m2 H1 H2; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA A0 a1); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA a1 A0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.
 
Theorem plusTerm_comp_l :
 forall a b c : Term,
 eqT a c -> eqT b c -> eqTerm a b -> eqTerm (plusTerm a c) (plusTerm b c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intuition.
Qed.
 
Theorem plusTerm_comp_r :
 forall a b c : Term,
 eqT c a -> eqT c b -> eqTerm a b -> eqTerm (plusTerm c a) (plusTerm c b).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intuition.
Qed.
 
Theorem plusTerm_com :
 forall x y : Term, eqT x y -> eqTerm (plusTerm x y) (plusTerm y x).
intros a b; case a; case b; simpl in |- *; auto.
Qed.
 
Theorem plusTerm_eqT1 :
 forall m1 m2 : Term, eqT m1 m2 -> eqT (plusTerm m1 m2) m1.
intros a b; case a; case b; simpl in |- *; auto.
Qed.
 
Theorem plusTerm_eqT2 :
 forall m1 m2 : Term, eqT m1 m2 -> eqT (plusTerm m1 m2) m2.
intros a b; case a; case b; simpl in |- *; auto.
Qed.
 
Theorem plusTerm_assoc :
 forall a a0 A1 : Term,
 eqT A1 a0 ->
 eqT a a0 ->
 eqTerm (plusTerm (plusTerm A1 a0) a) (plusTerm A1 (plusTerm a0 a)).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intuition.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs).
apply plusA_assoc with (1 := cs).
Qed.
 
Theorem eqTerm_plusTerm_comp :
 forall a b c d : Term,
 eqT a c ->
 eqT b d -> eqTerm a b -> eqTerm c d -> eqTerm (plusTerm a c) (plusTerm b d).
intros a b c d; case a; case b; case c; case d; simpl in |- *; auto.
intuition.
Qed.
Hint Resolve eqTerm_plusTerm_comp.


Set Implicit Arguments.
Unset Strict Implicit.
 
Definition multTerm : Term -> Term -> Term.
intros H'; case H'; intros b2 c2 H1'; case H1'; intros b3 c3;
 exact (multA b2 b3, mult_mon n c2 c3).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem zeroP_multTerm_l : forall a b : Term, zeroP a -> zeroP (multTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 H' b2 H'0 H'1;
 apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA A0 a1); 
 auto.
Qed.
 
Theorem zeroP_multTerm_r : forall a b : Term, zeroP a -> zeroP (multTerm b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 H' b2 H'0 H'1;
 apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA a1 A0); 
 auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA A0 a1); auto.
Qed.
 
Theorem multTerm_plusTerm_dist_l :
 forall a b c : Term,
 eqTerm (plusTerm (multTerm a c) (multTerm b c)) (multTerm (plusTerm a b) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a1 m1 a2 m2 a3 m3; split; auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 a3) (multA a1 a2));
 auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (multA a1 (plusA a3 a2)); auto.
Qed.
 
Theorem multTerm_plusTerm_dist_r :
 forall a b c : Term,
 eqTerm (plusTerm (multTerm c a) (multTerm c b)) (multTerm c (plusTerm a b)).
intros a b c; case a; case b; case c; simpl in |- *; auto.
Qed.
 
Theorem multTerm_eqT :
 forall a b c d : Term,
 eqT a b -> eqT c d -> eqT (multTerm a c) (multTerm b d).
intros a b c d; case a; case b; case c; case d; unfold eqT in |- *;
 simpl in |- *; auto.
intros H' c0 H'0 c2 H'1 c3 H'2 c4 H'3 H'4; rewrite H'3; rewrite H'4; auto.
Qed.
 
Theorem multTerm_assoc :
 forall a b c : Term,
 eqTerm (multTerm a (multTerm b c)) (multTerm (multTerm a b) c).
intros a b c; case a; case b; case c; simpl in |- *; auto.
intros a0 m a1 m0 a2 m1; split; auto.
apply multA_assoc with (1 := cs); auto.
apply mult_mon_assoc.
Qed.
 
Theorem multTerm_com :
 forall a b : Term, eqTerm (multTerm a b) (multTerm b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
apply mult_mon_com.
Qed.
 
Theorem eqTerm_multTerm_comp :
 forall a b c d : Term,
 eqTerm a b -> eqTerm c d -> eqTerm (multTerm a c) (multTerm b d).
intros a b c d; case a; case b; case c; case d; simpl in |- *; auto.
intros a1 m1 a2 m2 a3 m3 a4 m4; intros H1; case H1; intros H2 H3 H4; case H4;
 intros H5 H6; split; auto.
rewrite H3; rewrite H6; auto.
Qed.
Hint Resolve eqTerm_multTerm_comp.
 

Set Implicit Arguments.
Unset Strict Implicit.
 
Definition invTerm : Term -> Term.
intros H; case H; intros b2 c2; exact (invA b2, c2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem plusTerm_invTerm_zeroP :
 forall a : Term, zeroP (plusTerm a (invTerm a)).
intros a; case a; simpl in |- *; auto.
intros; apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); apply invA_plusA with (1 := cs);
 auto.
Qed.
 
Theorem zeroP_invTerm_zeroP : forall a : Term, zeroP a -> zeroP (invTerm a).
intros a; case a; simpl in |- *; auto.
intros b H' H'0;
 apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA A0 (invA A0)); 
 auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := invA A0); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := plusA (invA A0) A0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.
 
Theorem invTerm_invol : forall a : Term, eqTerm a (invTerm (invTerm a)).
intros a; case a; simpl in |- *; auto.
intros a0 m; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA a0 A0); auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA a0 (plusA (invA a0) (invA (invA a0)))); 
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (plusA a0 (invA a0)) (invA (invA a0))); 
 auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA A0 (invA (invA a0))); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (invA (invA a0)) A0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
Qed.
 
Theorem nZero_invTerm_nZero :
 forall a : Term, ~ zeroP a -> ~ zeroP (invTerm a).
intros a H'; red in |- *; intros H'0; absurd (zeroP a); auto.
apply zeroP_comp_eqTerm with (a := invTerm (invTerm a)); auto.
apply zeroP_invTerm_zeroP; auto.
apply eqTerm_sym; apply invTerm_invol; auto.
Qed.
Hint Resolve nZero_invTerm_nZero.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition T1 : Term.
exact (A1, M1).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem T1_nz : ~ zeroP T1.
simpl in |- *; auto.
apply A1_diff_A0 with (1 := cs).
Qed.
 
Theorem T1_multTerm_l :
 forall a b : Term, eqTerm a T1 -> eqTerm b (multTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H'; elim H'; intros H'0 H'1; rewrite H'1; clear H'; auto.
split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA A1 a0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs).
apply multA_A1_l with (1 := cs); auto.
apply multA_eqA_comp with (1 := cs); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply sym_eq; unfold M1 in |- *; apply mult_mon_zero_l.
Qed.
 
Theorem T1_multTerm_r :
 forall a b : Term, eqTerm a T1 -> eqTerm b (multTerm b a).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H'; elim H'; intros H'0 H'1; rewrite H'1; clear H'.
split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA a0 A1); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (y := multA A1 a0); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); apply multA_A1_l with (1 := cs); auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply sym_eq; unfold M1 in |- *; apply mult_mon_zero_r.
Qed.
 
Theorem nZero_invTerm_T1 : ~ zeroP (invTerm T1).
apply nZero_invTerm_nZero; auto.
exact T1_nz.
Qed.
Hint Resolve nZero_invTerm_T1.
 
Theorem mult_invTerm_com :
 forall a b : Term, eqTerm (multTerm (invTerm a) b) (invTerm (multTerm a b)).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA (invA a1) a0) A0);
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with
    (plusA (multA (invA a1) a0) (plusA (multA a1 a0) (invA (multA a1 a0))));
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with
    (plusA (plusA (multA (invA a1) a0) (multA a1 a0)) (invA (multA a1 a0)));
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA (plusA (invA a1) a1) a0) (invA (multA a1 a0))); 
 auto.
apply plusA_eqA_comp with (1 := cs); auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA a0 (invA a1)) (multA a0 a1)); 
 auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (multA a0 (plusA (invA a1) a1));
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA (plusA a1 (invA a1)) a0) (invA (multA a1 a0))); 
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA A0 a0) (invA (multA a1 a0))); 
 auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA A0 (invA (multA a1 a0)));
 auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs);
 apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (invA (multA a1 a0)) A0);
 auto.
Qed.
 
Theorem mult_invTerm_com_r :
 forall a b : Term, eqTerm (multTerm a (invTerm b)) (invTerm (multTerm a b)).
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0; split; auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (multA a1 (invA a0)) A0);
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with
    (plusA (multA a1 (invA a0)) (plusA (multA a1 a0) (invA (multA a1 a0))));
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with
    (plusA (plusA (multA a1 (invA a0)) (multA a1 a0)) (invA (multA a1 a0)));
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA a1 (plusA (invA a0) a0)) (invA (multA a1 a0))); 
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA a1 (plusA a0 (invA a0))) (invA (multA a1 a0))); 
 auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA a1 A0) (invA (multA a1 a0))); 
 auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs); auto.
apply
 (eqA_trans _ _ _ _ _ _ _ _ _ cs)
  with (plusA (multA A0 a1) (invA (multA a1 a0))); 
 auto.
apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA A0 (invA (multA a1 a0)));
 auto.
apply (eqA_sym _ _ _ _ _ _ _ _ _ cs);
 apply (eqA_trans _ _ _ _ _ _ _ _ _ cs) with (plusA (invA (multA a1 a0)) A0);
 auto.
Qed.
 
Theorem eqTerm_invTerm_comp :
 forall a b : Term, eqTerm a b -> eqTerm (invTerm a) (invTerm b).
intros a b; case a; case b; simpl in |- *; auto.
intuition.
Qed.
 
Theorem invTerm_eqT : forall a : Term, eqT a (invTerm a).
intros a; case a; simpl in |- *; auto.
Qed.
 
Theorem T1_eqT : forall a b : Term, eqTerm a T1 -> eqT b (multTerm a b).
intros a b; case a; case b; simpl in |- *; auto.
intros a1 m1 a2 m2 H1; case H1; intros H2 H3; auto.
rewrite H3; auto.
unfold eqT in |- *; simpl in |- *; apply sym_eq; unfold M1 in |- *;
 apply mult_mon_zero_l.
Qed.
 
Theorem eqTerm_T1_eqT : forall a : Term, eqTerm a T1 -> eqT a T1.
intros a; case a; simpl in |- *; auto.
intuition.
Qed.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition minusTerm : Term -> Term -> Term.
intros H; case H; intros b2 c2 H'; case H'; intros b3 c3;
 exact (minusA b2 b3, c2).
Defined.
Set Strict Implicit.
Unset Implicit Arguments.
 
Theorem eqTerm_minusTerm_plusTerm_invTerm :
 forall a b : Term, eqTerm (minusTerm a b) (plusTerm a (invTerm b)).
intros a b; case a; case b; simpl in |- *; auto.
split; auto.
apply minusA_def with (1 := cs); auto.
Qed.
 
Theorem minusTerm_eqT :
 forall m1 m2 : Term, eqT m1 m2 -> eqT (minusTerm m1 m2) m1.
intros a b; case a; case b; simpl in |- *; auto.
Qed.
 
Theorem zeroP_minusTerm : forall a : Term, zeroP (minusTerm a a).
intros a; apply zeroP_comp_eqTerm with (a := plusTerm a (invTerm a)); auto.
apply plusTerm_invTerm_zeroP; auto.
apply eqTerm_sym; apply eqTerm_minusTerm_plusTerm_invTerm; auto.
Qed.
 
Theorem multTerm_zeroP_div :
 forall a b : Term, zeroP (multTerm a b) -> zeroP a \/ zeroP b.
intros a b; case a; case b; simpl in |- *; auto.
intros a0 m a1 m0 H.
apply A_sep with (2 := eqA_dec) (1 := cs); auto.
Qed.
 
Theorem multTerm_minusTerm_dist_l :
 forall a b c : Term,
 eqT a b ->
 eqTerm (minusTerm (multTerm a c) (multTerm b c))
   (multTerm (minusTerm a b) c).
intros a b c eqT1.
apply eqTerm_trans with (y := multTerm (plusTerm a (invTerm b)) c); auto.
apply
 eqTerm_trans with (y := plusTerm (multTerm a c) (multTerm (invTerm b) c));
 auto.
apply
 eqTerm_trans with (y := plusTerm (multTerm a c) (invTerm (multTerm b c)));
 auto.
apply eqTerm_minusTerm_plusTerm_invTerm; auto.
apply eqTerm_plusTerm_comp; auto.
apply eqT_trans with (y := multTerm b c); auto.
apply multTerm_eqT; auto.
apply invTerm_eqT; auto.
apply multTerm_eqT; auto.
apply eqT_trans with (y := b); auto.
apply invTerm_eqT; auto.
apply eqTerm_refl; auto.
apply eqTerm_sym; apply mult_invTerm_com; auto.
apply multTerm_plusTerm_dist_l; auto.
apply eqTerm_multTerm_comp; auto.
apply eqTerm_sym; apply eqTerm_minusTerm_plusTerm_invTerm; auto.
apply eqTerm_refl; auto.
Qed.
Hint Resolve multTerm_minusTerm_dist_l.
 
Theorem nzeroP_multTerm :
 forall a b : Term, ~ zeroP a -> ~ zeroP b -> ~ zeroP (multTerm a b).
intros a b H' H'0; red in |- *; intros H'1;
 elim multTerm_zeroP_div with (a := a) (b := b); auto.
Qed.
End Term.