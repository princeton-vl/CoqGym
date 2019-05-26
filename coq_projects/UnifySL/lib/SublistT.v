Require Import Coq.Lists.List.

Inductive sublistT {A: Type}: list A -> list A -> Type :=
  | sublistT_nil_nil: sublistT nil nil
  | sublistT_cons: forall a {l1 l2}, sublistT l1 l2 -> sublistT l1 (a :: l2)
  | sublistT_cons_cons: forall a {l1 l2}, sublistT l1 l2 -> sublistT (a :: l1) (a :: l2).

Definition sublistT_refl {A: Type}: forall (l: list A), sublistT l l :=
  fix sublistT_refl l :=
    match l with
    | nil => sublistT_nil_nil
    | a :: l' => sublistT_cons_cons a (sublistT_refl l')
    end.

(*
Definition sublistT_trans {A: Type}:
  forall (l1 l2 l3: list A), sublistT l1 l2 -> sublistT l2 l3 -> sublistT l1 l3 :=
  fix sublistT_trans l1 l2 l3 g12 g23 :=
    match g23 with
    | 
*)