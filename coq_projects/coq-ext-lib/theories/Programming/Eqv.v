Require Import Equivalence.

Require Import ExtLib.Core.RelDec.

Class Eqv T := eqv : T -> T -> Prop.
Definition neg_eqv {T} {E:Eqv T} (x:T) (y:T) : Prop := not (eqv x y).

Class EqvWF T :=
{ eqvWFEqv :> Eqv T
; eqvWFEquivalence :> Equivalence eqv
}.
Instance EqvWF_Build {T} {E:Eqv T} {EV:Equivalence eqv} : EqvWF T :=
  { eqvWFEqv := E ; eqvWFEquivalence := EV }.

Definition eqv_dec {T} {E:Eqv T} {R:RelDec eqv} := rel_dec.
Definition neg_eqv_dec {T} {E:Eqv T} {R:RelDec eqv} x y := negb (rel_dec x y).

Section eqv_decP.
  Context {T} {E:Eqv T}.
  Context {RD:RelDec eqv} {RDC:RelDec_Correct RD}.
  Definition eqv_dec_p (x:T) (y:T) : {eqv x y} + {~eqv x y} := rel_dec_p x y.
  Definition neg_eqv_dec_p (x:T) (y:T) : {~eqv x y} + {eqv x y} := neg_rel_dec_p x y.
End eqv_decP.

Module EqvNotation.
  Infix "~=!" := eqv_dec (at level 35, no associativity).
  Infix "/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "~=" := eqv (at level 70, no associativity).
  Infix "/~=" := neg_eqv (at level 70, no associativity).
End EqvNotation.
Import EqvNotation.

Section injection_eqv_equivalence.
  Context {T U:Type}.
  Context {TE:EqvWF T}.
  Context {UE:Eqv U}.
  Variable (inj:U -> T).
  Variable injResp : forall u1 u2, u1 ~= u2 <-> inj u1 ~= inj u2.

  Definition injection_eqv_equivalence : Equivalence (eqv (T:=U)).
  Proof. repeat constructor ;
    unfold Reflexive ; unfold Symmetric ; unfold Transitive ; intros.
    apply injResp. reflexivity.
    apply injResp. apply injResp in H. symmetry. auto.
    apply injResp. apply injResp in H. apply injResp in H0.
    transitivity (inj y) ; auto.
  Qed.
End injection_eqv_equivalence.
