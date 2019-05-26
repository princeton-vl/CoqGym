From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Category.
From Categories Require Import Functor.Main.
From Categories Require Import Cat.Cat.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Archetypal.Discr.Discr.

(** The unique functor from the initial category to any other. *)
Program Definition Functor_From_Empty_Cat (C' : Category) : (0 –≻ C')%functor :=
{|
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => match a as _ return _ with end
|}.

Local Hint Extern 1 => cbn in *.

(** Empty Cat is the initial category. *)
Program Instance Cat_Init : (𝟘_ Cat)%object :=
{|
  terminal := 0%category;
  t_morph := fun x => Functor_From_Empty_Cat x
|}.
