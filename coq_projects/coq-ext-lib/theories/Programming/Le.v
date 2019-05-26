Require Import Coq.Bool.Bool.
Require Import Equivalence.
Require Import ExtLib.Core.RelDec.

Class Lte T := { lte : T -> T -> Prop }.
Definition neg_lte {T} {L:Lte T} (x:T) (y:T) : Prop := not (lte x y).

Definition lt {T} {L:Lte T} x y := lte x y /\ ~lte y x.
Definition neg_lt {T} {L:Lte T} x y := not (lt x y).

Instance lt_RelDec {T} {L:Lte T} {RD:RelDec lte} : RelDec lt :=
  { rel_dec x y := (rel_dec x y && negb (rel_dec y x))%bool }.

Instance lt_RelDecCorrect {T} {L:Lte T} {RD:RelDec lte} {RDC:RelDec_Correct RD}
  : RelDec_Correct lt_RelDec.
Proof. constructor.
  intros ; constructor ; intros.
  unfold rel_dec in H. simpl in H. apply andb_true_iff in H. destruct H.
    unfold lt. constructor. apply rel_dec_correct. auto.
    apply neg_rel_dec_correct. simpl in H0.
    apply negb_true_iff in H0. auto.
  unfold lt in H. destruct H. unfold rel_dec. simpl. apply andb_true_iff.
    constructor. apply rel_dec_correct. auto.
    apply negb_true_iff. apply neg_rel_dec_correct. auto.
Qed.

Class LteWF T :=
{ lteWFLte :> Lte T
; lteWFPreOrder :> PreOrder lte
}.

Instance LteWF_Build {T} {L:Lte T} {PO:PreOrder lte} : LteWF T :=
  { lteWFLte := L ; lteWFPreOrder := PO }.

Definition lte_dec {T} {L:Lte T} {R:RelDec lte} := rel_dec.
Definition neg_lte_dec {T} {L:Lte T} {R:RelDec lte} x y := negb (lte_dec x y).

Definition lt_dec {T} {L:Lte T} {R:RelDec lte} := rel_dec.
Definition neg_lt_dec {T} {L:Lte T} {R:RelDec lte} x y := negb (lt_dec x y).

Section dec_p.
  Context {T} {L:Lte T} {RD:RelDec lte} {DC:RelDec_Correct RD}.

  Definition lte_dec_p (x:T) (y:T) : {lte x y} + {~lte x y} := rel_dec_p x y.
  Definition neg_lte_dec_p (x:T) (y:T) : {~lte x y} + {lte x y} := neg_rel_dec_p x y.
  Definition lt_dec_p (x:T) (y:T) : {lt x y} + {~lt x y} := rel_dec_p x y.
  Definition neg_lt_dec_p (x:T) (y:T) : {~lt x y} + {lt x y} := neg_rel_dec_p x y.
End dec_p.

Module LteNotation.
  Notation "x <=! y"       := (lte_dec x y)
    (at level 35, no associativity).
  Notation "x <=! y <=! z" := (lte_dec x y /\ lte_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x >=! y"       := (lte_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x >=! y >=! z" := (lte_dec z y /\ lte_dec y x)
    (at level 35, y at next level, no associativity).

  Notation "x <! y"       := (lt_dec x y)
    (at level 35, no associativity).
  Notation "x <! y <! z"  := (lt_dec x y /\ lt_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x >! y"       := (lt_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x >! y >! z"  := (lt_dec z y /\ lt_dec y x)
    (at level 35, y at next level, no associativity).

  Notation "x <=? y"       := (lte_dec_p y x)
    (at level 35, no associativity).
  Notation "x <=? y <=? z" := (lte_dec_p x y /\ lte_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x >=? y"       := (lte_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x >=? y >=? z" := (lte_dec_p z y /\ lte_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x <? y"       := (lt_dec_p y x)
    (at level 35, no associativity).
  Notation "x <? y <? z"  := (lt_dec_p x y /\ lt_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x >? y"       := (lt_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x >? y >? z"  := (lt_dec_p z y /\ lt_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x <=. y"       := (lte x y)
    (at level 70, no associativity).
  Notation "x <=. y <=. z" := (lte x y /\ lte y z)
    (at level 70, y at next level, no associativity).
  Notation "x >=. y"       := (lte y x)
    (at level 70, no associativity, only parsing).
  Notation "x >=. y >=. z" := (lte z y /\ lte y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x <. y"       := (lt x y)
    (at level 70, no associativity).
  Notation "x <. y <. z" := (lt x y /\ lt y z)
    (at level 70, y at next level, no associativity).
  Notation "x >. y"       := (lt y x)
    (at level 70, no associativity, only parsing).
  Notation "x >. y >. z" := (lt z y /\ lt y x)
    (at level 70, y at next level, no associativity, only parsing).
End LteNotation.
