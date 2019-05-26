From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Const_Func.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.

(** The functor that maps each object c in C to the 
    constant functor that maps each object of D to c in Func_Cat D C. *)
Section Const_Func_Functor.
  Context (C D : Category).

  Program Definition Const_Func_Functor : (C –≻ (Func_Cat D C))%functor :=
    {|
      FO := fun c => Const_Func D c;
      FA := fun _ _ h => {|Trans := fun c => h|}
    |}.

End Const_Func_Functor.
