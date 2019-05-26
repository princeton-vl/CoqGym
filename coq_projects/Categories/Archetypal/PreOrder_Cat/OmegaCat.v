From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Archetypal.PreOrder_Cat.PreOrder_Cat.

Require Import Coq.Arith.Arith.

Delimit Scope omegacat_scope with omegacat.

Local Open Scope omegacat_scope.

(** Since we can't eliminate prop to define functors in a simple way,
we redefine the notion of le (less than or equal) for natural numbers
in Type (Tle).

We show that le implies Tle (and vise versa).

What follows are some properties of Tle.
 *)
Inductive Tle (n : nat) : nat → Type :=
| Tle_n : Tle n n
| Tle_S : ∀ m, Tle n m → Tle n (S m)
.

Hint Constructors Tle.

Notation "n ≤ m" := (Tle n m) : omegacat_scope.

Definition Tle_addS (n m : nat) : n ≤ m → S n ≤ S m.
Proof.
  intros H.
  induction H; auto.
Qed.

Definition Tle_trans (n m t : nat) : n ≤ m → m ≤ t → n ≤ t.
Proof.
  intros H1 H2.
  induction H2; auto.
Defined.

Definition Tle_remS (n m : nat) : S n ≤ S m → n ≤ m.
Proof.
  revert n.
  induction m.
  intros n H.
  induction n; auto.
  inversion H as [Hx | m H1 H2]; inversion H1.
  intros n H.
  inversion H; auto.
Qed.

Theorem Not_S_Tle (n : nat) : Tle (S n) n → False.
Proof.
  intros H.
  induction n; inversion H; auto.
  apply IHn.
  apply Tle_remS; trivial.
Qed.

(** Tle is decidable. This is crutial in conversion from le to Tle. *)
Definition Tle_dec (n m : nat) : (n ≤ m) + ((n ≤ m) → False).
Proof.
  revert m.
  induction n.
  - left; induction m; auto.
  - induction m.
    + right; intros H; inversion H.
    + destruct IHm as [H1|H1].
      left; auto.
      destruct (IHn m) as [H2|H2].
      * left; apply Tle_addS; trivial.
      * right.
        intros H3.
        contradict H2.
        apply Tle_remS; trivial.
Qed.

(** This is prety straightforward. *)
Definition Tle_le {n m : nat} : n ≤ m → le n m.
Proof.
  intros H.
  induction H; auto.
Qed.

(** The contrapositive of conversion from le to Tle. *)
Definition NTle_Nle {n m : nat} : (n ≤ m → False) → (le n m → False).
Proof.
  intros H1 H2.
  induction H2.
  + apply H1; trivial.
  + apply IHle.
    intros H3.
    apply H1; auto.
Qed.

(** This is the actual conversion from le to Tle.

Here, the trick is that we use decidability of Tle.
In case the relation holds, we have the proof.
In case it does not, we can refute the le relation.

Hence, this conversion is (as expected) does not
preform an explicit elimination of le (as it is
impossible) and hence is not computationally
simplifiable.
 *)
Definition le_Tle {n m : nat} : le n m → n ≤ m.
Proof.
  intros H.
  destruct (Tle_dec n m) as [H1|H1]; auto.
  contradict H.
  unfold not; apply NTle_Nle; trivial.
Qed.

(** We show that (homotopy-type-theoretically speaking) Tle is a mere
    proposition. That is, any two proofs of a ≤ b are equal. Note that
Tle is in Type and not in Pop and hence we can't use proof-irrelevance.

This is a proof in a hurry, and can perhaps be simplified later.
 *)
Theorem Tle_is_HProp {n m : nat} (H H' : Tle n m) : H = H'.
Proof.
  dependent induction H.
  dependent induction H'; trivial.
  {
    inversion H' as [H1| m' H1 H2].
    {
      contradict H1; clear.
      induction m; auto.
    }
    {
      subst.
      contradict H1; clear.
      induction m'.
      + intros H; inversion H.
      + intros H.
        apply IHm'.
        apply Tle_remS; trivial.
    }
  }
  {
    inversion H'.
    + subst.
      clear IHTle.
      contradict H; clear.
      intros H.
      induction m.
      * inversion H.
      * apply IHm.
        apply Tle_remS; trivial.
    + subst.
      dependent destruction H'.
      {
        clear IHTle.
        contradict H; clear.
        intros H.
        induction m.
        * inversion H.
        * apply IHm.
          apply Tle_remS; trivial.
      }
      {
        apply f_equal.
        apply IHTle.
      }
  }
Qed.

(** Natural numbers form a preorder with le (less than or equal relation). *)
Definition OmegaPreOrder :=
  {|
    PreOrder_car := nat : Type;
    PreOrder_rel := Tle : _ → _ → Type;
    PreOrder_rel_isProp :=
      fun _ _ h h' => Tle_is_HProp h h';
    PreOrder_refl := Tle_n;
    PreOrder_trans := Tle_trans
  |}.

(** The pre-order category ω. *)
Definition OmegaCat : Category := PreOrder_Cat OmegaPreOrder.

Notation "'ω'" := (OmegaCat) : omegacat_scope.

Lemma le_Tle_n (n : nat) : le_Tle (le_n n) = Tle_n n.
Proof.
  apply Tle_is_HProp.
Qed.

Lemma le_Tle_S (n m : nat) (H : le n m) :
  le_Tle (le_S _ _ H) = Tle_S _ _ (le_Tle H).
Proof.
  apply Tle_is_HProp.
Qed.

Lemma le_Tle_trans (n m k : nat) (H : le n m) (H' : le m k) :
  le_Tle (le_trans _ _ _ H H') = Tle_trans _ _ _ (le_Tle H) (le_Tle H').
Proof.
  apply Tle_is_HProp.
Qed.

(** Given a map f from natural numbers to objects of a category C
and a map from (f (S n) –≻ f n), we construct a functor from
ωᵒᵖ to C. *)
(** This is the arrow map of the functor being constructed. *)
Local Fixpoint FA_fx {C : Category}
      (OOF_O : nat → C)
      (OOF_A : ∀ n, ((OOF_O (S n)) –≻ (OOF_O n))%morphism)
      (n m : nat) (h : Tle n m)
      {struct h} : (OOF_O m –≻ OOF_O n)%morphism
  :=
    match h in _ ≤ w return
          (OOF_O w –≻ OOF_O n)%morphism
    with
    | Tle_n _ =>
      id (OOF_O n)
    | Tle_S _ m' H' =>
      ((FA_fx OOF_O OOF_A _ _ H') ∘ (OOF_A m'))%morphism
    end
.

(** This is the the functor described above. *)
Program Definition OmegaCat_Op_Func {C : Category}
      (OOF_O : nat → C)
      (OOF_A : ∀ n, ((OOF_O (S n)) –≻ (OOF_O n))%morphism)
  : ((ω^op) –≻ C)%functor :=
  {|
    FO := OOF_O;
    FA := fun m n h => FA_fx OOF_O OOF_A _ _ h
  |}
.

Next Obligation.
Proof.
  induction f as [|m t IHt].
  + cbn; auto.
  + replace (Tle_trans _ _ _ g (Tle_S _ _ t))
    with (Tle_S _ _ (Tle_trans _ _ _ g t)).
    cbn.
    rewrite IHt.
    auto.
    apply Tle_is_HProp.
Qed.

(** Similar functor from ω to C. *)
Definition OmegaCat_Func {C : Category}
           (OMF_O : nat → C)
           (OMF_A : ∀ n, ((OMF_O n) –≻ (OMF_O (S n)))%morphism)
  : (OmegaCat –≻ C)%functor
  := (@OmegaCat_Op_Func (C^op) OMF_O OMF_A)^op.

(** Any functor from ωᵒᵖ to C is freely generated by its object map and the
    image of the arrow map under (le_S _ _ (le_n n)) (proof of (le n (S n))). *)
Lemma OmegaCat_Op_Func_unique {C : Category} (F : ((ω^op) –≻ C)%functor) :
  F = OmegaCat_Op_Func (FO F) (fun n => FA F (Tle_S _ _ (Tle_n n))).
Proof.
  Func_eq_simpl.
  extensionality y.
  extensionality x.
  extensionality h.
  cbn in *.
  revert x y h.
  induction x.
  {
    intros y h.
    induction y.
    + dependent destruction h.
      rewrite (F_id F).
      trivial.
    + dependent destruction h.
      cbn in *.
      rewrite <- (IHy h).
      rewrite <- F_compose.
      match goal with
        [|- (F _a)%morphism ?A = (F _a)%morphism ?B] =>
        set (l := A); set (l' := B); cbn in l, l'; PIR
      end.
      trivial.
  }
  {
    intros y h.
    induction y.
    + inversion h.
    + dependent destruction h.
      * rewrite (F_id F).
        trivial.
      * cbn.
        rewrite <- (IHy h).
        rewrite <- F_compose.
        match goal with
          [|- (F _a)%morphism ?A = (F _a)%morphism ?B] =>
          set (l := A); set (l' := B); cbn in l, l'; PIR
        end.
        trivial.
  }
Qed.

(** Any functor from ω to C is freely generated by its object map and the image
    of the arrow map under (le_S _ _ (le_n n)) (proof of (le n (S n))). *)
Lemma OmegaCat_Func_unique {C : Category} (F : (ω –≻ C)%functor) :
  F = OmegaCat_Func (FO F) (fun n => FA F (Tle_S _ _ (Tle_n n))).
Proof.
  unfold OmegaCat_Func.
  cbn_rewrite <- ((OmegaCat_Op_Func_unique (F^op))).
  trivial.
Qed.
