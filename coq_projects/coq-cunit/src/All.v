Require Import Coq.Lists.List.

Import ListNotations.

(** Some useful functions on lists. *)
Module List.
  Fixpoint map_pair {A B C : Type} (f : A -> B -> C) (l : list (A * B))
    : list C :=
    match l with
    | [] => []
    | (a, b) :: l => f a b :: map_pair f l
    end.

  Fixpoint map_triple {A B C D : Type} (f : A -> B -> C -> D)
    (l : list (A * B * C)) : list D :=
    match l with
    | [] => []
    | (a, b, c) :: l => f a b c :: map_triple f l
    end.

  Fixpoint map_quad {A B C D E : Type} (f : A -> B -> C -> D -> E)
    (l : list (A * B * C * D)) : list E :=
    match l with
    | [] => []
    | (a, b, c, d) :: l => f a b c d :: map_quad f l
    end.
End List.
