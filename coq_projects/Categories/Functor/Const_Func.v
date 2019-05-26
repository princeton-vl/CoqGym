From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor.

(** A constant functor maps all objects to a single object and all
    arrows to identity arrow of that object. *)
Section Const_Func.
  Context (C : Category) {D : Category} (a : @Obj D).

  Program Definition Const_Func : (C –≻ D)%functor :=
    {|
      FO := fun _ => a;
      FA := fun _ _ _ => id a
    |}.

End Const_Func.
