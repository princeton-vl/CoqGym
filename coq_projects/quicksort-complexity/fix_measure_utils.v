
Set Implicit Arguments.

Require Import Le.
Require Import Lt.
Require Import Arith.
Require Import Recdef.
Require Coq.Program.Wf.
Require List.

Section measure_wf.

  (* Measure relations are well-founded if the underlying relation is well-founded. *)

  Variables T M: Set.
  Variable R: M -> M -> Prop.
  Hypothesis wf: well_founded R.
  Variable m: T -> M.

  Definition MR (x y: T): Prop := R (m x) (m y).

  Lemma measure_wf: well_founded MR.
  Proof with auto.
    unfold well_founded.
    cut (forall a: M, forall a0: T, m a0 = a -> Acc MR a0).
      intros.
      apply (H (m a))...
    apply (@well_founded_ind M R wf (fun mm => forall a, m a = mm -> Acc MR a)).
    intros.
    apply Acc_intro.
    intros.
    unfold MR in H1.
    rewrite H0 in H1.
    apply (H (m y))...
  Defined.

End measure_wf.

Section Fix_measure_rects.

  Variable A: Set.
  Variable R: A -> A -> Prop.
  Variable Rwf: well_founded R.
  Variable P: A -> Type.
  Variable f: forall x: A, (forall y: { y: A | R y x }, P (proj1_sig y)) -> P x.

  Lemma F_unfold x r:
    Wf.Fix_F_sub A R P f x r =
    f (fun y => Wf.Fix_F_sub A R P f (proj1_sig y) (Acc_inv r (proj2_sig y))).
  Proof. intros. case r; auto. Qed.

  (* F_sub_rect lets one prove a property of functions defined using Wf.Fix_measure_F_sub by showing that property to be invariant over single application of the function body (f in our case). *)

  Lemma F_sub_rect
    (Q: forall x, P x -> Type)
    (inv: forall x: A,
     (forall (y: A) (H: R y x) (a: Acc R y),
        Q y (Wf.Fix_F_sub A R P f y a)) ->
        forall (a: Acc R x),
          Q x (f (fun y: {y: A | R y x} =>
            Wf.Fix_F_sub A R P f (proj1_sig y) (Acc_inv a (proj2_sig y)))))
    : forall x a, Q _ (Wf.Fix_F_sub A R P f x a).
  Proof with auto.
    set (R' := fun (x: A) => forall a, Q _ (Wf.Fix_F_sub A R P f x a)).
    cut (forall x, R' x)...
    apply (well_founded_induction_type Rwf).
    subst R'.
    simpl.
    intros.
    rewrite F_unfold...
  Qed.

  (* Let's call f's second parameter its "lowers" function, since it provides it access to results for inputs with a lower measure.

  In preparation of lemma similar to F_sub_rect, but for Wf.Fix_measure_sub (which is what Program uses), we first need an extra hypothesis stating that the function body has the same result for different "lowers" functions (g and h below) as long as those produce the same results for lower inputs, regardless of the lt proofs. *)

  Hypothesis equiv_lowers:
    forall x0 (g h: forall x: {y: A | R y x0}, P (proj1_sig x)),
    (forall x p p', g (exist (fun y: A => R y x0) x p) = h (exist _ x p')) ->
      f g = f h.

  (* From equiv_lowers, it follows that [Wf.Fix_measure_F_sub A m P f x] applications do not not depend on the Acc proofs. *)

  Lemma eq_F_sub x: forall (a a': Acc R x),
    Wf.Fix_F_sub A R P f x a =
    Wf.Fix_F_sub A R P f x a'.
  Proof.
    intro a.
    pattern x, (Wf.Fix_F_sub A R P f x a).
    apply F_sub_rect.
    intros.
    rewrite F_unfold.
    apply equiv_lowers.
    intros.
    apply H.
    assumption.
  Qed.

  Lemma unfold x:
    Wf.Fix_sub A R Rwf P f x =
    f (fun y => Wf.Fix_sub A R Rwf P f (proj1_sig y)).
  Proof. intros. unfold Wf.Fix_sub.
    rewrite F_unfold.
    apply equiv_lowers.
    intros.
    apply eq_F_sub.
  Qed.

  (* Finally, Fix_measure_F_rect lets one prove a property of functions defined using Wf.Fix_measure_F by showing that property to be invariant over single application of the function body (f). *)

  Lemma rect
    (Q: forall x, P x -> Type)
    (inv: forall
      (x: A)
      (H: forall (y: A), R y x -> Q y (Wf.Fix_sub A R Rwf P f y))
      (a: Acc R x),
        Q x (f (fun y: {y: A | R y x} => Wf.Fix_sub A R Rwf P f (proj1_sig y))))
    : forall x, Q _ (Wf.Fix_sub A R Rwf P f x).
  Proof with auto.
    unfold Wf.Fix_sub.
    intros.
    apply F_sub_rect.
    intros.
    assert (forall y: A, R y x0 -> Q y (Wf.Fix_F_sub A R P f y (Rwf y)))...
    set (inv x0 X0 a). clearbody q.
    rewrite <- (equiv_lowers (fun y: {y: A | R y x0} => Wf.Fix_F_sub A R P f (proj1_sig y) (Rwf (proj1_sig y))) (fun y: {y: A | R y x0} => Wf.Fix_F_sub A R P f (proj1_sig y) (Acc_inv a (proj2_sig y))))...
    intros.
    apply eq_F_sub.
  Qed.

End Fix_measure_rects.

Module Example.

  Import List.

  Definition tail (l: list nat): list nat :=
    match l with
    | nil => nil
    | _ :: t => t
    end.

  Program Fixpoint bla (l: list nat) {measure (length l) on lt}: nat :=
    match l with
    | nil => 3
    | _ => bla (tail l) + 2
    end.

  Next Obligation.
    destruct l.
      elimtype False. apply H. reflexivity.
    simpl. apply le_refl.
  Qed.

  (* We can now prove a property about bla, using Fix_measure_sub_rect to do induction corresponding to bla's recursion. *)

  Goal forall x, 3 <= bla x.
  Proof with auto.
    intro x.
    pattern (bla x).
    set (fun n : nat => 3 <= n).
    unfold bla.
    generalize x. clear x.
    apply rect; intros.
      destruct x0...
    subst P.
    simpl.
    destruct x...
    replace 3 with (3 + 0)...
    apply plus_le_compat...
    apply H.
    unfold Wf.MR...
  Qed.

End Example.
