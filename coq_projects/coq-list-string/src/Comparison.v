(** Comparison functions. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Char.
Require Import LString.

Import ListNotations.
Import LString.

(** Total order on strings. *)
Fixpoint compare (x y : t) : comparison :=
  match x, y with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | x :: xs, y :: ys =>
    match Char.compare x y with
    | Eq => compare xs ys
    | c => c
    end
  end.

Lemma compare_implies_eq : forall (x y : t), compare x y = Eq -> x = y.
  induction x as [|a x HI]; destruct y as [|b y]; simpl; try congruence.
  case_eq (Char.compare a b); simpl; try congruence.
  now intros Hab Hxy; rewrite (Char.compare_implies_eq _ _ Hab); rewrite (HI _ Hxy).
Qed.

Lemma compare_same_is_eq : forall (x : t), compare x x = Eq.
  intro x; induction x; simpl; trivial.
  now rewrite Char.compare_same_is_eq; rewrite IHx.
Qed.

(** Test if two strings are equal. *)
Definition eqb (x y : t) : bool :=
  match compare x y with
  | Eq => true
  | _ => false
  end.

Lemma eqb_implies_eq : forall (x y : t), eqb x y = true -> x = y.
  intros x y; unfold eqb; case_eq (compare x y); try congruence.
  now intros; apply compare_implies_eq.
Qed.

Lemma eqb_same_is_eq : forall (x : t), eqb x x = true.
  now intros; unfold eqb; rewrite compare_same_is_eq.
Qed.

(** Decide the equality of two strings. *)
Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  case_eq (eqb x y); intro Heqb; [left | right].
  - now apply eqb_implies_eq.
  - intro Heq; rewrite Heq in Heqb.
    rewrite eqb_same_is_eq in Heqb; congruence.
Defined.
