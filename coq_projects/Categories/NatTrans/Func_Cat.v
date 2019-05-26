From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import Cat.Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations.

(** The category of functors.

– Objects: functors from C to C'
– Arrows: natural transformations
*)
Program Definition Func_Cat (C C' : Category) : Category :=
{|
  Obj := (C –≻ C')%functor;

  Hom := NatTrans;

  compose := @NatTrans_compose _ _;

  id := @NatTrans_id _ _;

  assoc := fun _ _ _ _ _ _ _ => @NatTrans_compose_assoc _ _ _ _ _ _ _ _ _;
             
  assoc_sym :=
    fun _ _ _ _ _ _ _ => eq_sym (@NatTrans_compose_assoc _ _ _ _ _ _ _ _ _);

  id_unit_right := @NatTrans_id_unit_right _ _;
  
  id_unit_left := @NatTrans_id_unit_left _ _
|}.

Section Opposite_Func_Cat.
  Context (C D : Category).

  (** Functor from functor category to its opposite. Maps each functor
       to its opposite. *)
  Program Definition Op_Func_Cat_to_Func_Cat_Op
    : ((Func_Cat C D)^op –≻ (Func_Cat (C^op) (D^op)))%functor :=
    {|
      FO := Opposite_Functor;
      FA := fun _ _ => Opposite_NatTrans;
      F_id := fun _ => NatTrans_id_Op _;
      F_compose := fun _ _ _ _ _ => NatTrans_compose_Op _ _ 
    |}.

  (** Functor from the opposite of a functor category to it. Maps each functor
      to its opposite. *)
  Program Definition Func_Cat_Op_to_Op_Func_Cat
    : ((Func_Cat (C^op) (D^op)) –≻ (Func_Cat C D)^op)%functor :=
    {|
      FO := Opposite_Functor;
      FA := fun _ _ => Opposite_NatTrans;
      F_id := fun F => NatTrans_id_Op F;
      F_compose := fun _ _ _ N N' => NatTrans_compose_Op N N'
    |}.
  
  (** The opposite of the category of functors from C to D is naturally
       isomorphic to the category of functors from C^op to D^op. *)
  Program Definition Func_Cat_Op_Iso
    : ((((Func_Cat C D)^op)%category)
         ≃≃ (Func_Cat (C^op) (D^op)) ::> Cat) %isomorphism :=
    {|
      iso_morphism := Op_Func_Cat_to_Func_Cat_Op;
      inverse_morphism := Func_Cat_Op_to_Op_Func_Cat
    |}.

End Opposite_Func_Cat.
