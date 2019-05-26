From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.

Local Open Scope functor_scope.

(** Cat, the category of (small) categories, is a category whose objects are
    (small) categories and morphisms are functors.

In this development, the (relative) smallness/largeness is represented by
universe levels and universe polymorphism of Coq.
*)
Definition Cat : Category :=
{|
  Obj := Category;

  Hom := Functor;

  compose := fun C D E => Functor_compose;
  
  assoc := fun C D E F (G : C –≻ D) (H : D –≻ E) (I : E –≻ F) =>
            @Functor_assoc _ _ _ _ G H I;

  assoc_sym := fun C D E F (G : C –≻ D) (H : D –≻ E) (I : E –≻ F) =>
            eq_sym (@Functor_assoc _ _ _ _ G H I);

  id := fun C => Functor_id C;

  id_unit_left := fun C D => @Functor_id_unit_left C D;

  id_unit_right := fun C D => @Functor_id_unit_right C D          
|}.
