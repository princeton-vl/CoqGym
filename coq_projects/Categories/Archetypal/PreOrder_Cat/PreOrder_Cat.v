From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.

(** Every pre-order relation is a category. *)
Record PreOrder : Type :=
{
  PreOrder_car :> Type;
  
  PreOrder_rel :> PreOrder_car → PreOrder_car → Type
  where "a ≤ b" := (PreOrder_rel a b);

  PreOrder_rel_isProp : ∀ x y (h h' : PreOrder_rel x y), h = h'; 

  PreOrder_refl : ∀ a, a ≤ a;

  PreOrder_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c
}.

Arguments PreOrder_rel {_} _ _.
Arguments PreOrder_refl {_} _.
Arguments PreOrder_trans {_ _ _ _} _ _.

Notation "a ≤ b" := (PreOrder_rel a b) : preorder_scope.

Section PreOrder_Cat.
  Context (P : PreOrder).

  Local Hint Resolve PreOrder_rel_isProp.

  Program Definition PreOrder_Cat : Category :=
    {|
      Obj := P;
      Hom := fun a b => (a ≤ b)%preorder;
      compose := @PreOrder_trans P;
      id := @PreOrder_refl P
    |}
  .
  
End PreOrder_Cat.
