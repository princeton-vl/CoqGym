Module Option.
  Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
    match x with
    | Some x => f x
    | None => None
    end.

  Definition map {A B} (x : option A) (f : A -> B) : option B :=
    match x with
    | Some x => Some (f x)
    | None => None
    end.

  Definition default {A} (x : option A) (d : A) : A :=
    match x with
    | Some x => x
    | None => d
    end.
End Option.

Module Sum.
  Definition bind {E A B} (x : A + E) (f : A -> B + E) : B + E :=
    match x with
    | inl x => f x
    | inr e => inr e
    end.

  Definition map {E A B} (x : A + E) (f : A -> B) : B + E :=
    match x with
    | inl x => inl (f x)
    | inr e => inr e
    end.

  Definition default {E A} (x : A + E) (d : A) : A :=
    match x with
    | inl x => x
    | inr _ => d
    end.
End Sum.
