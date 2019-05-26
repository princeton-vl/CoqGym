Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint repeat_aux {A : Type} (x : A) (n : nat) (l : list A) : list A :=
  match n with
  | O => l
  | S n => repeat_aux x n (x :: l)
  end.

(** Make a list of `n` elements `x`. *)
Definition repeat {A : Type} (x : A) (n : nat) : list A :=
  repeat_aux x n [].

(** Remove the elements `None` of a list. *)
Fixpoint remove_nones {A : Type} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | None :: l => remove_nones l
  | Some x :: l => x :: remove_nones l
  end.

(** Do a map removing the `None` results of `f`. *)
Fixpoint map_filter {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l =>
    match f x with
    | None => map_filter f l
    | Some y => y :: map_filter f l
    end
  end.
