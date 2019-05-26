From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.

(** A presheaf on C is a functor Cᵒᵖ –≻ Type_Cat. *)
Definition PreSheaf (C : Category) := Functor (C^op) Type_Cat.

(** The category of presheaves. *)
Definition PShCat (C : Category) := Func_Cat (C^op) Type_Cat.
