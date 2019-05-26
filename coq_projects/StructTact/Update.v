Require Import StructTact.StructTactics.
Require Import FunctionalExtensionality.

Definition update {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) st h (v : B) := 
  fun nm => if A_eq_dec nm h then v else st nm.

Section update.
  Variables A B : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Lemma update_diff :
    forall (sigma : A -> B) x v y,
      x <> y ->
      update A_eq_dec sigma x v y = sigma y.
  Proof using.
    unfold update.
    intros.
    break_if; congruence.
  Qed.

  Lemma update_nop :
    forall (sigma : A -> B) x y,
      update A_eq_dec sigma x (sigma x) y = sigma y.
  Proof using.
    unfold update.
    intros. break_if; congruence.
  Qed.

  Lemma update_eq :
    forall (sigma : A -> B) x y v,
      x = y ->
      update A_eq_dec sigma x v y = v.
  Proof using.
    intros. subst.
    unfold update.
    break_if; congruence.
  Qed.

  Lemma update_same :
    forall (sigma : A -> B) x v,
      update A_eq_dec sigma x v x = v.
  Proof using.
    intros.
    rewrite update_eq; auto.
  Qed.

  Lemma update_nop_ext :
    forall (sigma : A -> B) h,
      update A_eq_dec sigma h (sigma h) = sigma.
  Proof using.
    intros.
    apply functional_extensionality.
    intros.
    apply update_nop.
  Qed.

  Lemma update_nop_ext' :
    forall (sigma : A -> B) y v,
      sigma y = v ->
      update A_eq_dec sigma y v = sigma.
  Proof using.
    intros.
    subst.
    apply update_nop_ext.
  Qed.

  Lemma update_overwrite :
    forall (sigma : A -> B) h st st',
      update A_eq_dec (update A_eq_dec sigma h st) h st' = update A_eq_dec sigma h st'.
  Proof using.
    intros.
    apply functional_extensionality.
    intros. destruct (A_eq_dec h x).
    - repeat rewrite update_eq; auto.
    - repeat rewrite update_diff; auto.
  Qed.
End update.

Lemma update_fun_comm :
  forall A B C A_eq_dec (f : B -> C) (st : A -> B) y v x,
    f (update A_eq_dec st y v x) = update A_eq_dec (fun x => f (st x)) y (f v) x.
Proof.
  intros.
  destruct (A_eq_dec x y); subst;
    repeat first [rewrite update_diff by congruence |
                  rewrite update_eq  by auto ]; auto.
Qed.

Ltac update_destruct_goal :=
  match goal with
    | [ |- context [ update ?eq_dec _ ?y _ ?x ] ] => destruct (eq_dec y x)
  end.

Ltac update_destruct_hyp :=
  match goal with
    | [ _ : context [ update ?eq_dec _ ?y _ ?x ] |- _ ] => destruct (eq_dec y x)
  end.

Ltac update_destruct := update_destruct_goal || update_destruct_hyp.

Ltac rewrite_update' H :=
  first [rewrite update_diff in H by congruence |
         rewrite update_eq in H by auto ].

Ltac rewrite_update :=
  repeat match goal with
           | [ H : context [ update _ _ _ _ _ ] |- _ ] =>
             rewrite_update' H; repeat rewrite_update' H
           | [ |- _ ] => repeat (try rewrite update_diff by congruence;
                                 try rewrite update_eq by auto)
         end.

Ltac destruct_update :=
  repeat (update_destruct; subst; rewrite_update).

Ltac destruct_update_hyp :=
  repeat ((update_destruct_hyp || update_destruct_goal); subst; rewrite_update).

Ltac update_destruct_simplify :=
  update_destruct; subst; rewrite_update; simpl in *.

Ltac update_destruct_simplify_hyp :=
  update_destruct_hyp || update_destruct_goal; subst; rewrite_update; simpl in *.

Ltac update_destruct_max_simplify :=
  update_destruct; subst_max; rewrite_update; simpl in *.
