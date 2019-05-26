(** Associativity lists. *)
Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint add {A B} (eqb : A -> A -> bool) (l : list (A * B)) (k : A) (v : B)
  : list (A * B) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: l =>
    if eqb k k' then
      (k, v) :: l
    else
      (k', v') :: add eqb l k v
  end.

Fixpoint find {A B} (eqb : A -> A -> bool) (l : list (A * B)) (k : A)
  : option B :=
  match l with
  | [] => None
  | (k', v) :: l =>
    if eqb k k' then
      Some v
    else
      find eqb l k
  end.

Fixpoint remove {A B} (eqb : A -> A -> bool) (l : list (A * B)) (k : A)
  : list (A * B) :=
  match l with
  | [] => l
  | (k', v) :: l =>
    if eqb k k' then
      l
    else
      (k', v) :: remove eqb l k
  end.

Module Test.
  Require Import Coq.Arith.EqNat.

  Definition add_nil {A B} (eqb : A -> A -> bool) (k : A) (v : B)
    : add eqb [] k v = [(k, v)] :=
    eq_refl.

  Definition add_nat_1
    : add beq_nat [(2, 4); (3, 6)] 3 7 = [(2, 4); (3, 7)] :=
    eq_refl.

  Definition add_nat_2
    : add beq_nat [(2, 4); (3, 6)] 4 7 = [(2, 4); (3, 6); (4, 7)] :=
    eq_refl.

  Definition find_nil {A B} (eqb : A -> A -> bool) (k : A)
    : find (B := B) eqb [] k = None :=
    eq_refl.

  Definition find_nat_1 : find beq_nat [(2, 4); (3, 6)] 3 = Some 6 :=
    eq_refl.

  Definition find_nat_2 : find beq_nat [(2, 4); (3, 6)] 4 = None :=
    eq_refl.

  Definition remove_nil {A B} (eqb : A -> A -> bool) (k : A)
    : remove (B := B) eqb [] k = [] :=
    eq_refl.

  Definition remove_nat_1
    : remove beq_nat [(2, 4); (3, 6)] 3 = [(2, 4)] :=
    eq_refl.

  Definition remove_nat_2
    : remove beq_nat [(2, 4); (3, 6)] 4 = [(2, 4); (3, 6)] :=
    eq_refl.
End Test.
