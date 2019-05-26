Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R)
  {struct n}: well_founded R :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro x (fun y _ => guard n (guard n wfR) y)
  end.

Section setoid_fix.
  Variables (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R).
  Variables (P : A -> Type)
            (F : forall x : A, (forall y : A, R y x -> P y) -> P x).
  Variable r : forall x : A, P x -> P x -> Prop.
  Hypothesis Hstep : forall (x : A) (f g : forall y : A, R y x -> P y),
                       (forall (y : A) (p : R y x), r (f y p) (g y p)) ->
                       r (@F x f) (@F x g).

  Lemma Fix_F_equiv_inv
  : forall (x : A) (r' s' : Acc R x),
      r (Fix_F _ F r') (Fix_F _ F s').
  Proof.
    intro x; induction (Rwf x); intros.
    rewrite <- (Fix_F_eq _ F r'); rewrite <- (Fix_F_eq _ F s'); intros.
    eapply Hstep.
    eauto.
  Qed.

  Theorem Fix_equiv
  : forall x : A,
      r (Fix Rwf P F x) (@F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)).
  Proof.
    intro x; unfold Fix.
    rewrite <- Fix_F_eq.
    apply Hstep; intros.
    apply Fix_F_equiv_inv.
  Qed.
End setoid_fix.