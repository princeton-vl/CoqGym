(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Matric computation *)

Require Import Arith Omega Eqdep_dec ZArith.

Require Import utils_tac gcd prime binomial sums.

Set Implicit Arguments.

Section rings.

  Variable (R : Type) (Rzero Rone : R) (Rplus Rmult Rminus : R -> R -> R) (Ropp : R -> R)
           (R_is_ring : ring_theory Rzero Rone Rplus Rmult Rminus Ropp eq). 

  Infix "⊕" := Rplus (at level 50, left associativity).
  Infix "⊗" := Rmult (at level 40, left associativity).

  Notation z := Rzero.
  Notation o := Rone.
  Notation "∸" := Ropp.

  (* ⊕  ⊗  ∸ *)

  (* We use the magical parameterized ring tactic *)

  Add Ring Rring : R_is_ring.

  (* ⊕  ⊗  ∸ *)

  (*   ( a b )   <-> (a,b,c,d) 
       ( c d )                    *)

  Definition M22 := (R * R * R * R)%type.
  Definition ID_22 : M22 := (o,z,z,o).
  Definition ZE_22 : M22 := (z,z,z,z).

  Definition PL22 : M22 -> M22 -> M22.
  Proof.
    intros (((a,b),c),d) (((a',b'),c'),d').
    exact (a⊕a',b⊕b',
           c⊕c',d⊕d').
  Defined.

  Infix "⊞" := PL22 (at level 50, left associativity).
 
  Definition MI22 : M22 -> M22.
  Proof.
    intros (((a,b),c),d).
    exact (∸a,∸b,
           ∸c,∸d).
  Defined.

  Notation "⊟" := MI22.

  Fact M22_equal (a b c d a' b' c' d' : R) : a = a' -> b = b' -> c = c' -> d = d' -> (a,b,c,d) = (a',b',c',d').
  Proof. intros; subst; trivial. Qed.

  Fact M22plus_zero : forall m, ZE_22 ⊞ m = m.
  Proof. 
    intros (((a,b),c),d); apply M22_equal; ring.
  Qed.

  Fact M22plus_comm  : forall x y, x ⊞ y = y ⊞ x.
  Proof.
    intros (((a,b),c),d) (((a',b'),c'),d'); apply M22_equal; ring.
  Qed.

  Fact M22plus_assoc  : forall x y u, x ⊞ (y ⊞ u) = x ⊞ y ⊞ u.
  Proof.
    intros (((a,b),c),d) (((a',b'),c'),d') (((a'',b''),c''),d''); simpl; apply M22_equal; ring. 
  Qed.

  Fact M22minus : forall x, x ⊞ ⊟ x = ZE_22.
  Proof.
    intros (((a,b),c),d); apply M22_equal; ring.
  Qed.

  Fact M22plus_cancel : forall x a b, x ⊞ a = x ⊞ b -> a = b.
  Proof.
    intros x a b H.
    rewrite <- (M22plus_zero a), <- (M22minus x), (M22plus_comm x), 
            <- M22plus_assoc, H, M22plus_assoc,
            (M22plus_comm _ x), M22minus, M22plus_zero.
    trivial.
  Qed.

  Theorem M22plus_monoid : monoid_theory PL22 ZE_22.
  Proof.
    exists.
    + apply M22plus_zero.
    + intro; rewrite M22plus_comm; apply M22plus_zero.
    + intros; apply M22plus_assoc.
  Qed.

  Definition MU22 : M22 -> M22 -> M22.
  Proof.
    intros (((a,b),c),d) (((a',b'),c'),d').
    exact (a⊗a' ⊕ b⊗c' , a⊗b' ⊕ b⊗d',
           c⊗a' ⊕ d⊗c' , c⊗b' ⊕ d⊗d' ).
  Defined.

  Infix "⊠" := MU22 (at level 40, left associativity).

  Tactic Notation "myauto" integer(n) := do n intros (((?&?)&?)&?); apply M22_equal; ring.

  Fact M22mult_one_l : forall x, ID_22 ⊠ x = x.
  Proof. myauto 1. Qed.

  Fact M22mult_one_r : forall x, x ⊠ ID_22 = x.
  Proof. myauto 1. Qed.

  Fact M22mult_assoc : forall x y u, x ⊠ (y ⊠ u) = x ⊠ y ⊠ u.
  Proof. myauto 3. Qed.

  Fact M22_mult_distr_l : forall x y u, x ⊠ (y⊞u) = x⊠y ⊞ x⊠u.
  Proof. myauto 3. Qed.
 
  Fact M22_mult_distr_r : forall x y u, (y⊞u) ⊠ x = y⊠x ⊞ u⊠x.
  Proof. myauto 3. Qed.

  Theorem M22mult_monoid : monoid_theory MU22 ID_22.
  Proof.
    exists.
    + apply M22mult_one_l.
    + apply M22mult_one_r.
    + apply M22mult_assoc.
  Qed.

  Fact M22_opp_mult_l : forall x y, (⊟ x) ⊠ y = ⊟ (x ⊠ y).
  Proof. myauto 2. Qed.

  Fact M22_opp_mult_r : forall x y, x ⊠ (⊟y) = ⊟ (x ⊠ y).
  Proof. myauto 2. Qed.

  Definition M22scal (k : R) : M22 -> M22.
  Proof.
    intros (((u,v),w),z).
    exact (k⊗u,k⊗v,k⊗w,k⊗z).
  Defined.

  Fact M22scal_mult k1 k2 : forall x, M22scal k1 (M22scal k2 x) = M22scal (k1⊗k2) x.
  Proof. myauto 1. Qed.

  Fact M22scal_PL22 k : forall x y, M22scal k (x ⊞ y) = M22scal k x ⊞ M22scal k y.
  Proof. myauto 2. Qed.

  Fact M22scal_MI22 : forall x, M22scal (∸o) x = ⊟x.
  Proof. myauto 1. Qed.

  Fact M22scal_zero : forall x, M22scal z x = ZE_22.
  Proof. myauto 1. Qed.

  Fact M22scal_MU22_l k : forall x y, M22scal k (x ⊠ y) = M22scal k x ⊠ y.
  Proof. myauto 2. Qed.

  Fact M22scal_MU22_r k : forall x y, M22scal k (x ⊠ y) = x ⊠ M22scal k y.
  Proof. myauto 2. Qed.

  Fact mscal_M22scal n x : mscal PL22 ZE_22 n x = M22scal (mscal Rplus Rzero n Rone) x.
  Proof.
    induction n as [ | n IHn ].
    + do 2 rewrite mscal_0; revert x; myauto 1.
    + do 2 rewrite mscal_S.
      rewrite IHn; clear IHn.
      revert x; myauto 1.
  Qed.

  (* M22 is NOT a ring because mult is not commutative *)

  (* ⊕  ⊗  ∸    ⊞ ⊠ ⊟ *)

  Definition Det22 : M22 -> R.
  Proof.
    intros (((a,b),c),d).
    exact (a⊗d ⊕ ∸(b⊗c)).
  Defined.

  Fact Det22_scal k : forall x, Det22 (M22scal k x) = (k ⊗ k) ⊗ Det22 x.
  Proof. intros (((?,?),?),?); simpl; ring. Qed.

  Fact Det22_mult : forall x y, Det22 (x⊠y) = Det22 x ⊗ Det22 y.
  Proof. intros (((?,?),?),?) (((?,?),?),?); simpl; ring. Qed.

  Notation expo22 := (mscal MU22 ID_22).
  Notation expoR := (mscal Rmult o).

  Fact expo22_scal k n U : expo22 n (M22scal k U) = M22scal (expoR n k) (expo22 n U).
  Proof.
    induction n as [ | n IHn ].
    + do 3 rewrite mscal_0; apply M22_equal; ring.
    + do 3 rewrite mscal_S.
      rewrite IHn.
      rewrite <- M22scal_MU22_l, <- M22scal_MU22_r.
      rewrite M22scal_mult; auto.
  Qed.

  Fact Det22_expo n x : Det22 (expo22 n x) = expoR n (Det22 x).
  Proof.
    induction n as [ | n IHn ].
    + do 2 rewrite mscal_0; simpl; ring.
    + do 2 rewrite mscal_S.
      rewrite Det22_mult, IHn; ring.
  Qed.

  Fact Diag22_expo n x y : expo22 n (x,z,z,y) = (expoR n x,Rzero,Rzero,expoR n y).
  Proof.
    induction n as [ | n IHn ]; try (simpl; auto; fail).
    do 3 rewrite mscal_S; rewrite IHn.
    apply M22_equal; ring.
  Qed.

  Fact MU22_Diag22 a b c d x y : (a,b,c,d) ⊠ (x,z,z,y) = (a⊗x,b⊗y,c⊗x,d⊗y).
  Proof. apply M22_equal; ring. Qed.
 
  (* We also the to lift the Z -> Zp morphism to M22 matrices *)

  Fact M22_proj12 a1 b1 c1 d1 a2 b2 c2 d2 : (a1,b1,c1,d1) = (a2,b2,c2,d2) :> M22 -> c1 = c2.
  Proof. inversion 1; auto. Qed.

End rings.

Section ring_morphism.

  Variable (X : Type) (zX oX : X) (pX mX : X -> X -> X) (oppX : X -> X)
           (Y : Type) (zY oY : Y) (pY mY : Y -> Y -> Y) (oppY : Y -> Y).

  Variable phi : X -> Y.

  Notation "〚 x 〛" := (phi x).

  Record ring_morphism : Prop := mk_ring_morph {
    morph_z : 〚 zX 〛= zY;
    morph_o : 〚 oX 〛= oY;
    morph_plus : forall x y, 〚 pX x y 〛= pY 〚 x 〛〚 y 〛;
    morph_mult : forall x y, 〚 mX x y 〛= mY 〚 x 〛〚 y 〛;
    morph_opp : forall x, 〚 oppX x 〛= oppY 〚 x 〛;
  }.

  Hypothesis Hphi : ring_morphism.

  Definition morph22 : M22 X -> M22 Y.
  Proof.
    intros (((a,b),c),d).
    exact (〚 a 〛, 〚 b 〛,
           〚 c 〛, 〚 d 〛).
  Defined.

  Tactic Notation "myauto" integer(n) := do n intros (((?&?)&?)&?); apply M22_equal; ring.

  Fact PL22_morph : forall x y, morph22 (PL22 pX x y) = PL22 pY (morph22 x) (morph22 y).
  Proof. 
    destruct Hphi.
    do 2 intros (((?&?)&?)&?); apply M22_equal; auto.
  Qed.

  Fact MU22_morph : forall x y, morph22 (MU22 pX mX x y) = MU22 pY mY (morph22 x) (morph22 y).
  Proof. 
    destruct Hphi as [ G1 G2 G3 G4 G6 ].
    do 2 intros (((?&?)&?)&?); apply M22_equal; 
      repeat rewrite G3; repeat rewrite G4; auto.
  Qed.

  Fact MI22_morph : forall x, morph22 (MI22 oppX x) = MI22 oppY (morph22 x).
  Proof. 
    destruct Hphi as [ G1 G2 G3 G4 G6 ].
    do 1 intros (((?&?)&?)&?); apply M22_equal; 
      repeat rewrite G3; repeat rewrite G4; auto.
  Qed.

  Fact M22scal_morph : forall k x, morph22 (M22scal mX k x) = M22scal mY 〚 k 〛 (morph22 x).
  Proof.
    destruct Hphi as [ G1 G2 G3 G4 G6 ].
    intros k (((?&?)&?)&?); apply M22_equal; auto.
  Qed.

  Fact Det22_morph : forall x, 〚 Det22 pX mX oppX x 〛= Det22 pY mY oppY (morph22 x).
  Proof.
    destruct Hphi as [ G1 G2 G3 G4 G6 ].
    intros (((?&?)&?)&?); simpl.
    rewrite G3, G6, G4, G4; auto.
  Qed.

  Fact expo22_morph n x : morph22 (mscal (MU22 pX mX) (ID_22 zX oX) n x)
                        = mscal (MU22 pY mY) (ID_22 zY oY) n (morph22 x).
  Proof.
    destruct Hphi as [ G1 G2 G3 G4 G6 ].
    induction n as [ | n IHn ].
    + do 2 rewrite mscal_0; apply M22_equal; auto.
    + do 2 rewrite mscal_S.
      rewrite MU22_morph, IHn; auto.
  Qed.

End ring_morphism.

