(* Usual option type *)

Inductive Option (A : Set) : Set :=
  | Some : forall x : A, Option A
  | None : Option A.