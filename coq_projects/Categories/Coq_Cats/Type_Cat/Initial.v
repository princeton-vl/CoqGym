From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 3.

(** The empty type is the initial object of category of types. *)
Program Instance Empty_init : (𝟘_ Type_Cat)%object :=
  {|terminal := (Empty : Type)|}.
