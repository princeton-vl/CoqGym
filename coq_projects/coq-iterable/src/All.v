Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import FunctionNinjas.All.

Import ListNotations.
Local Open Scope N.

Module Iterable.
  Class C (T A : Type) : Type := {
    iter : forall {S E : Type},
      S -> (S -> A -> S + E) -> T -> S + E }.

  Module Instance.
    Instance list (A : Type) : C (list A) A := {
      iter := fun S E =>
        fix iter (s : S) (f : S -> A -> S + E) (l : list A) : S + E :=
          match l with
          | [] => inl s
          | x :: l =>
            match f s x with
            | inl s => iter s f l
            | inr e => inr e
            end
          end }.

    Instance string : C string Ascii.ascii := {
      iter := fun S E =>
        fix iter (s : S) (f : S -> Ascii.ascii -> S + E) (l : string) : S + E :=
          match l with
          | EmptyString => inl s
          | String x l =>
            match f s x with
            | inl s => iter s f l
            | inr e => inr e
            end
          end }.
  End Instance.

  Definition fold {T A : Type} `{C T A} {S : Type} (s : S)
    (f : S -> A -> S) (l : T) : S :=
    match iter (E := Empty_set) s (fun s x => inl @@ f s x) l with
    | inl x => x
    | inr e => match e with end
    end.

  Definition length {T A : Type} `{C T A} (l : T) : N :=
    fold 0 (fun n _ => N.succ n) l.
End Iterable.