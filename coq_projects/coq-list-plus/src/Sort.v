Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint merge {A : Type} (leb : A -> A -> bool) (l1 l2 : list A) : list A :=
  let fix aux (l2 : list A) : list A :=
    match (l1, l2) with
    | ([], _) => l2
    | (_, []) => l1
    | (x1 :: l1, x2 :: l2) =>
      if leb x1 x2 then
        x1 :: merge leb l1 (x2 :: l2)
      else
        x2 :: aux l2
    end in
  aux l2.

Module Stack.
  Definition t (A : Type) := list (option (list A)).

  Fixpoint add {A : Type} (leb : A -> A -> bool) (s : t A) (l : list A) : t A :=
    match s with
    | [] => [Some l]
    | None :: s => Some l :: s
    | Some l' :: s => None :: add leb s (merge leb l l')
    end.

  Fixpoint of_list {A : Type} (leb : A -> A -> bool) (l : list A) : t A :=
    match l with
    | [] => []
    | x :: l => add leb (of_list leb l) [x]
    end.

  Fixpoint to_list {A : Type} (leb : A -> A -> bool) (s : t A) : list A :=
    match s with
    | [] => []
    | None :: s => to_list leb s
    | Some l :: s => merge leb l (to_list leb s)
    end.
End Stack.

Definition sort {A : Type} (leb : A -> A -> bool) (l : list A) : list A :=
  Stack.to_list leb (Stack.of_list leb l).

Module Test.
  Require Import Coq.Arith.Compare_dec.

  Definition l := [5; 1; 3; 7; 8 ;0; 0; 3 ;6 ;5 ;4].
  Definition sorted_l := [0; 0; 1; 3; 3; 4; 5; 5; 6; 7; 8].
  
  Definition ok : sort leb l = sorted_l :=
    eq_refl.
End Test.
