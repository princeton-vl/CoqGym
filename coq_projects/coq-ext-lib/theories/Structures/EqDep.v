Require Coq.Logic.Eqdep_dec.
Require EquivDec.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Section Classes.
  Context {A : Type}.
  Context {dec : EquivDec.EqDec A (@eq A)}.

  Theorem UIP_refl : forall {x : A} (p1 : x = x), p1 = refl_equal _.
    intros.
    eapply Coq.Logic.Eqdep_dec.UIP_dec. apply EquivDec.equiv_dec.
  Qed.

  Theorem UIP_equal : forall {x y : A} (p1 p2 : x = y), p1 = p2.
    eapply Coq.Logic.Eqdep_dec.UIP_dec. apply EquivDec.equiv_dec.
  Qed.

  Lemma inj_pair2 :
    forall (P:A -> Type) (p:A) (x y:P p),
      existT P p x = existT P p y -> x = y.
  Proof.
    intros. eapply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec; auto.
  Qed.

  Theorem equiv_dec_refl_left : forall a, @EquivDec.equiv_dec _ _ _ dec a a = left eq_refl.
  Proof.
    intros. destruct (EquivDec.equiv_dec a a); try congruence.
    f_equal. apply UIP_equal.
  Qed.

End Classes.

Section from_rel_dec.
  Variable T : Type.
  Variable RD : RelDec (@eq T).
  Variable RDC : RelDec_Correct RD.

  Global Instance EqDec_RelDec : EquivDec.EqDec T (@eq T).
  Proof.
    red; intros.
    consider (x ?[ eq ] y); intros; subst; auto.
    left. reflexivity.
  Qed.
End from_rel_dec.
