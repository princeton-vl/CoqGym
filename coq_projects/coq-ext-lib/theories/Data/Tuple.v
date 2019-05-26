Require Import ExtLib.Data.Fin.

Set Implicit Arguments.
Set Strict Implicit.
Set Asymmetric Patterns.

Fixpoint vector (T : Type) (n : nat) : Type :=
  match n with
    | 0 => unit
    | S n => prod T (vector T n)
  end.

Fixpoint get {T} {n : nat} (f : fin n) : vector T n -> T :=
  match f in fin n return vector T n -> T with
    | F0 n => fun v : T * vector T n => fst v
    | FS n f => fun v : T * vector T n => get f (snd v)
  end.

Fixpoint put {T} {n : nat} (f : fin n) (t : T) : vector T n -> vector T n :=
  match f in fin n return vector T n -> vector T n with
    | F0 _ => fun v => (t, snd v)
    | FS _ f => fun v => (fst v, put f t (snd v))
  end.

Theorem get_put_eq : forall {T n} (v : vector T n) (f : fin n) val,
  get f (put f val v) = val.
Proof.
  induction n.
  { inversion f. }
  { remember (S n). destruct f.
    inversion Heqn0; subst; intros; reflexivity.
    inversion Heqn0; subst; simpl; auto. }
Qed.

Theorem get_put_neq : forall {T n} (v : vector T n) (f f' : fin n) val,
  f <> f' ->
  get f (put f' val v) = get f v.
Proof.
  induction n.
  { inversion f. }
  { remember (S n); destruct f.
    { inversion Heqn0; clear Heqn0; subst; intros.
      destruct (fin_case f'); try congruence.
      destruct H0; subst. auto. }
    { inversion Heqn0; clear Heqn0; subst; intros.
      destruct (fin_case f').
      subst; auto.
      destruct H0; subst. simpl.
      eapply IHn. congruence. } }
Qed.

Definition vector_tl {T : Type} {n : nat} (v : vector T (S n)) : vector T n :=
  snd v.

Definition vector_hd {T : Type} {n : nat} (v : vector T (S n)) : T :=
  fst v.
