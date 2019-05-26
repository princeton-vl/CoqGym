(* This code is copyrighted by its authors; it is distributed under  *)
(* the terms of the LGPL license (see LICENSE and description files) *)

Require Export CoefStructure.
Section mCoef.
Load "hCoefStructure".
Load "mCoefStructure".
 
Let eqA_trans := eqA_trans _ _ _ _ _ _ _ _ _ cs.
 
Let eqA_sym := eqA_sym _ _ _ _ _ _ _ _ _ cs.
 
Theorem eqA_A0 : forall a b : A, eqA a A0 -> eqA a b -> eqA b A0.
intros a b H H1; apply eqA_trans with (y := a); auto.
Qed.
 
Theorem plusA_eqA_comp_l :
 forall a b c : A, eqA a b -> eqA (plusA a c) (plusA b c).
intros a b c H'; auto.
Qed.
 
Theorem plusA_eqA_comp_r :
 forall a b c : A, eqA a b -> eqA (plusA c a) (plusA c b).
intros a b c H'; auto.
Qed.
 
Theorem eqA0_left : forall a b : A, eqA a A0 -> eqA b (plusA a b).
intros a b H'; apply eqA_trans with (y := plusA A0 b); auto.
apply eqA_trans with (y := plusA b A0); auto.
Qed.
 
Theorem eqA0_right : forall a b : A, eqA b A0 -> eqA a (plusA a b).
intros a b H'; apply eqA_trans with (y := plusA a A0); auto.
Qed.
 
Theorem invA0 : eqA A0 (invA A0).
apply eqA_trans with (y := plusA A0 (invA A0)); auto.
apply eqA_trans with (y := plusA (invA A0) A0); auto.
Qed.
 
Theorem invA0_comp : forall a : A, eqA a A0 -> eqA a (invA a).
intros a H'; apply eqA_sym; apply eqA_trans with (y := A0); auto.
apply eqA_trans with (y := invA A0); auto.
apply eqA_sym; apply invA0; auto.
Qed.
 
Theorem invA0_inv : forall a : A, eqA a (invA (invA a)).
intros a.
apply eqA_trans with (y := plusA a A0); auto.
apply eqA_trans with (y := plusA A0 a); auto.
apply eqA_trans with (y := plusA (plusA (invA a) (invA (invA a))) a); auto.
apply eqA_trans with (y := plusA (plusA (invA (invA a)) (invA a)) a); auto.
apply eqA_trans with (y := plusA (invA (invA a)) (plusA (invA a) a)); auto.
apply eqA_trans with (y := plusA (invA (invA a)) (plusA a (invA a))); auto.
apply eqA_trans with (y := plusA (invA (invA a)) A0); auto.
Qed.
 
Theorem multA_eqA_comp_l :
 forall a b c : A, eqA a b -> eqA (multA a c) (multA b c).
intros a b c H'; auto.
Qed.
 
Theorem multA_eqA_comp_r :
 forall a b c : A, eqA a b -> eqA (multA c a) (multA c b).
intros a b c H'; auto.
Qed.
 
Theorem multA_dist_r :
 forall a b c : A, eqA (plusA (multA a c) (multA b c)) (multA (plusA a b) c).
intros a b c; apply eqA_trans with (y := plusA (multA c a) (multA c b)); auto.
apply eqA_trans with (y := multA c (plusA a b)); auto.
Qed.
 
Theorem multA_A0_r : forall a : A, eqA (multA a A0) A0.
intros a; apply eqA_trans with (y := multA A0 a); auto.
Qed.
 
Theorem multA_A1_r : forall a : A, eqA (multA a A1) a.
intros a; apply eqA_trans with (y := multA A1 a); auto.
Qed.
Hint Resolve multA_A1_r.
 
Theorem multA_invA_com_l :
 forall a b : A, eqA (multA (invA a) b) (invA (multA a b)).
intros a b; apply eqA_trans with (y := plusA (invA (multA a b)) A0); auto.
apply eqA_trans with (y := plusA A0 (invA (multA a b))); auto.
apply eqA_trans with (y := plusA (multA A0 b) (invA (multA a b))); auto.
apply
 eqA_trans with (y := plusA (multA (plusA a (invA a)) b) (invA (multA a b)));
 auto.
apply
 eqA_trans
  with (y := plusA (plusA (multA a b) (multA (invA a) b)) (invA (multA a b)));
 auto.
apply
 eqA_trans
  with (y := plusA (plusA (multA (invA a) b) (multA a b)) (invA (multA a b)));
 auto.
apply
 eqA_trans
  with (y := plusA (multA (invA a) b) (plusA (multA a b) (invA (multA a b))));
 auto.
apply eqA_trans with (y := plusA (multA (invA a) b) A0); auto.
apply plusA_eqA_comp with (1 := cs); auto.
apply multA_dist_r.
Qed.
Hint Resolve multA_invA_com_l.
 
Theorem multA_invA_com_r :
 forall a b : A, eqA (multA a (invA b)) (invA (multA a b)).
intros a b; apply eqA_trans with (y := multA (invA b) a); auto.
apply eqA_trans with (y := invA (multA b a)); auto.
Qed.
Hint Resolve multA_invA_com_r.
 
Theorem divA_multA_comp_l :
 forall (a b c : A) (nZc : ~ eqA c A0),
 eqA (divA (multA a b) c nZc) (multA a (divA b c nZc)).
intros a b c nZc; apply eqA_trans with (y := divA (multA b a) c nZc); auto.
apply eqA_trans with (y := multA (divA b c nZc) a); auto.
apply divA_multA_comp_r with (1 := cs); auto.
Qed.
Hint Resolve divA_multA_comp_l.
 
Theorem invA_is_invA1 : forall a : A, eqA (invA a) (multA (invA A1) a).
intros a; apply eqA_trans with (y := plusA (invA a) A0); auto.
apply eqA_trans with (y := plusA (invA a) (multA A0 a)); auto.
apply eqA_trans with (y := plusA (invA a) (multA (plusA A1 (invA A1)) a));
 auto.
apply
 eqA_trans
  with (y := plusA (invA a) (plusA (multA A1 a) (multA (invA A1) a))); 
 auto.
apply plusA_eqA_comp with (1 := cs); auto.
apply eqA_sym; auto.
apply multA_dist_r.
apply eqA_trans with (y := plusA (invA a) (plusA a (multA (invA A1) a)));
 auto.
apply eqA_trans with (y := plusA (plusA (invA a) a) (multA (invA A1) a));
 auto.
apply eqA_trans with (y := plusA (plusA a (invA a)) (multA (invA A1) a));
 auto.
apply eqA_trans with (y := plusA A0 (multA (invA A1) a)); auto.
apply eqA_trans with (y := plusA (multA (invA A1) a) A0); auto.
Qed.
 
Theorem divA_A0_l : forall (a : A) (nZa : ~ eqA a A0), eqA (divA A0 a nZa) A0.
intros a nZa; apply eqA_trans with (y := divA (multA A0 a) a nZa).
apply divA_eqA_comp with (1 := cs); auto.
apply eqA_trans with (y := multA A0 (divA a a nZa)); auto.
Qed.
Hint Resolve divA_A0_l.
 
Theorem A_sep : forall a b : A, eqA (multA a b) A0 -> eqA a A0 \/ eqA b A0.
intros a b H'; case (eqA_dec a A0); auto; case (eqA_dec b A0); auto.
intros nZb nZa; case nZa.
apply eqA_trans with (y := multA (divA a b nZb) b); auto.
apply divA_is_multA with (1 := cs); auto.
apply eqA_trans with (y := divA (multA a b) b nZb); auto.
apply eqA_sym; apply divA_multA_comp_r with (1 := cs); auto.
apply eqA_trans with (y := divA A0 b nZb); auto.
Qed.
Hint Resolve A_sep.
 
Theorem divA_A1 : forall (a : A) (nZa : ~ eqA a A0), eqA (divA a a nZa) A1.
intros a nZa; apply eqA_trans with (y := divA (multA A1 a) a nZa); auto.
apply eqA_trans with (y := multA (divA A1 a nZa) a); auto.
apply divA_multA_comp_r with (1 := cs); auto.
apply eqA_sym; apply divA_is_multA with (1 := cs); auto.
Qed.
Hint Resolve divA_A1.
 
Theorem divA_nZ :
 forall a b : A,
 ~ eqA b A0 -> forall nZa : ~ eqA a A0, ~ eqA (divA b a nZa) A0.
intros a b H' nZa; red in |- *; intros H'1; auto.
case H'; apply eqA_trans with (y := multA (divA b a nZa) a); auto.
apply divA_is_multA with (1 := cs); auto.
apply eqA_trans with (y := multA A0 a); auto.
Qed.
Hint Resolve divA_nZ.
End mCoef.