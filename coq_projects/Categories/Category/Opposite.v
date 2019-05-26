From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Category.

(** The oposite of a category C is a category with the same objects where the arrows are inverted. 
As a result, f ∘_Cᵒᵖ g is just g ∘_C f and consequently, assoc is assoc_sym (reversed with arrow
arguments) and vice versa. Similarly, id_unit_left and id_unit_right are also swapped. *)

Definition Opposite (C : Category) : Category :=
{|

  Obj := Obj C;
           
  Hom := fun a b => (b –≻ a)%morphism;

  compose :=
    fun a b c (f : (b –≻ a)%morphism) (g : (c –≻ b)%morphism) => compose C c b a g f;

  id := fun c => id C c;
  
  assoc := fun _ _ _ _ f g h => assoc_sym h g f;

  assoc_sym := fun _ _ _ _ f g h => assoc h g f;

  id_unit_left := fun _ _ h => @id_unit_right C _ _ h;
  
  id_unit_right := fun _ _ h => @id_unit_left C _ _ h
                   
|}.

Notation "C '^op'" := (Opposite C) : category_scope.
