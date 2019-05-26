Definition apply {A B} (f : A -> B) (x : A) := f x.

Notation " x |> f " := (apply f x)
  (at level 40, left associativity).

Notation " f @@ x " := (apply f x)
  (at level 42, right associativity).