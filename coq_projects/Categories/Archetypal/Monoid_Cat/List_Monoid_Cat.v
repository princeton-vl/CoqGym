From Categories Require Import Category.Main.
From Categories Require Import Archetypal.Monoid_Cat.Monoid_Cat.
Require Import Coq.Lists.List.

(** Lists form a monoid and thus a category. *)
Section List_Monoid_Cat.
  Context (A : Type).

  Hint Resolve app_assoc app_nil_r.

  Program Definition List_Monoid : Monoid :=
    {|
      Mon_car := list A;

      Mon_op := fun a b => (a ++ b)%list;

      Mon_unit := nil
    |}.

  Definition List_Monoid_Cat := Monoid_Cat List_Monoid.

End List_Monoid_Cat.
