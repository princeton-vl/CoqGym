
Set Implicit Arguments.
Unset Strict Implicit.

Require Export List.

Section Listes.

  Variable A : Set.

  Let List := list A.



  Inductive item (x : A) : List -> nat -> Prop :=
    | item_hd : forall l : List, item x (x :: l) 0
    | item_tl :
        forall (l : List) (n : nat) (y : A),
        item x l n -> item x (y :: l) (S n).

  Lemma fun_item :
   forall (u v : A) (e : List) (n : nat), item u e n -> item v e n -> u = v.
Proof.
simple induction 1; intros.
inversion_clear H0; auto.

inversion_clear H2; auto.
Qed.


  Lemma list_item :
   forall e n, {t : _ | item t e n} + {(forall t, ~ item t e n)}.
Proof.
fix item_rec 1.
intros [| h l].
right; red in |- *; intros t in_nil; inversion in_nil.

intros [| k].
left; exists h; constructor.

case (item_rec l k).
intros (y, in_tl); left; exists y; constructor; trivial.

intros not_in_tl; right; intros t in_tl_l; inversion_clear in_tl_l;
 red in not_in_tl; eauto.
Defined.



  Inductive trunc : nat -> List -> List -> Prop :=
    | trunc_O : forall e : List, trunc 0 e e
    | trunc_S :
        forall (k : nat) (e f : List) (x : A),
        trunc k e f -> trunc (S k) (x :: e) f.

  Lemma item_trunc :
   forall (n : nat) (e : List) (t : A),
   item t e n -> exists f : List, trunc (S n) e f.
Proof.
simple induction n; intros.
inversion_clear H.
exists l.
apply trunc_S.
apply trunc_O.

inversion_clear H0.
elim H with l t; intros.
exists x.
apply trunc_S.
trivial.

trivial.
Qed.


End Listes.

  Hint Resolve item_hd item_tl trunc_O trunc_S: core.

