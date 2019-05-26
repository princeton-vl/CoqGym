From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.

(** The terminal object in category C is an object t such that for any object a,
    there is a unique arrow ! : a -> t. *)
Class Terminal (C : Category) : Type :=
{
  terminal : C;
  t_morph : ∀ (d : Obj), (d –≻ terminal)%morphism;
  t_morph_unique : ∀ (d : Obj) (f g : (d –≻ terminal)%morphism), f = g
}.

Arguments terminal {_} _.
Arguments t_morph {_} _ _.
Arguments t_morph_unique {_} _ _ _ _.

Coercion terminal : Terminal >-> Obj.

Notation "𝟙_ C" := (Terminal C) (at level 75) : object_scope.

(** (The) terminal object is unique up to isomorphism. *)
Theorem Terminal_iso {C : Category} (T T' : (𝟙_ C)%object) :
  (T ≃ T')%isomorphism.
Proof.
  apply (Build_Isomorphism _ _ _ (t_morph _ _) (t_morph _ _));
  apply t_morph_unique.
Qed.

(** The initial is the dual of the terminal object. *)
Definition Initial (C : Category) := (𝟙_ (C ^op))%object.
Existing Class Initial.

Notation "𝟘_ C" := (Initial C) (at level 75) : object_scope.
