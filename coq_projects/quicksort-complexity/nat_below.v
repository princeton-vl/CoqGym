Global Set Automatic Coercions Import.
Set Implicit Arguments.

Require Import Arith.
Require Compare_dec.
Require EqNat.
Require Import Omega.

Fixpoint cond_eq (T: nat -> Set) n m {struct n}: forall c, T (c + n) -> T (c + m) -> Prop :=
  match n, m return forall c, T (c + n) -> T (c + m) -> Prop with
  | 0, 0 => fun c x y => x = y
  | S n', S m' => fun c x y => cond_eq T n' m' (S c)
      (eq_rec_r T x (plus_n_Sm c n'))
      (eq_rec_r T y (plus_n_Sm c m'))
  | _, _ => fun _ _ _ => True
  end.

Lemma cond_eq_eq (T: nat -> Set) n c (x y: T (c + n)): cond_eq T n n c x y = (x = y).
Proof with auto.
  induction n in c, x, y |- *...
  simpl.
  intros.
  rewrite IHn.
  unfold eq_rec_r.
  unfold eq_rec.
  unfold eq_rect.
  simpl plus.
  case (sym_eq (plus_n_Sm c n))...
Qed.

Lemma cond_eq_neq (T: nat -> Set) n m c (x: T (c + n)) (y: T (c + m)): n <> m -> cond_eq T n m c x y = True.
Proof with auto.
  induction n in m, c, x, y |- *...
    destruct m...
    intros.
    elimtype False...
  destruct m...
  intros.
  simpl.
  apply IHn.
  intro.
  apply H.
  subst...
Qed.

Inductive natBelow: nat -> Set := mkNatBelow (v p: nat): natBelow (S (v + p)).

Definition nb_val {n: nat} (nb: natBelow n): nat := match nb with mkNatBelow m _ => m end.

Coercion nb_val: natBelow >-> nat.

Lemma natBelow_unique n (x y: natBelow n): nb_val x = nb_val y -> x = y.
Proof with auto.
  cut (forall n (x: natBelow n) m (y: natBelow m), nb_val x = nb_val y -> cond_eq natBelow n m 0 x y); [|clear x y]; intros.
    set (H n x n y H0).
    rewrite cond_eq_eq in c...
  destruct x.
  destruct y.
  simpl in H.
  subst.
  destruct (eq_nat_dec p p0).
    subst.
    rewrite cond_eq_eq...
  rewrite cond_eq_neq...
  intro.
  omega.
Qed.

Lemma natBelow_uneq n (x y: natBelow n): nb_val x <> nb_val y -> x <> y.
Proof. intros. intro. subst. auto. Qed.

Lemma natBelow_eq_dec n (x y: natBelow n): { x = y } + { x <> y }.
Proof with auto.
  intros. destruct (eq_nat_dec x y); [left | right].
    apply natBelow_unique...
  apply natBelow_uneq...
Qed.

Definition nb0 n: natBelow (S n) := mkNatBelow 0 n.

Definition Snb n (nb: natBelow n): natBelow (S n) :=
  match nb in (natBelow n0) return (natBelow (S n0)) with
  | mkNatBelow v p => mkNatBelow (S v) p
  end.
