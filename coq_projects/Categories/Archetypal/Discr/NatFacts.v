From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Ext_Cons.Arrow.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Cat.Cat Cat.Cat_Iso.
From Categories Require Import NatTrans.NatTrans NatTrans.NatIso.
From Categories Require Import Archetypal.Discr.Discr.

(** This module contains facts about discrete categories and discrete
    functors involving natural transformations. *)

(** The fact that dicrete functor from (Discr_Cat A) to Cᵒᵖ is naturally
    isomorphic to the opposite of discrete-opposite functor
    from (Discr_Cat A)ᵒᵖ to C. *)
Section Discr_Func_Iso.
  Context {C : Category} {A : Type} (Omap : A → C).

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Discr_Func_Iso :
    (
      (@Discr_Func (C^op) A Omap) ≃ ((@Discr_Func_op C A Omap)^op)%functor
    )%natiso
    :=
      {|
        iso_morphism :=
          {|
            Trans := fun _ => id
          |};
        inverse_morphism :=
          {|
            Trans := fun _ => id
          |}
      |}
  .
    
End Discr_Func_Iso.

(** We show that the opposite of the functor from the singleton category that
maps to object x in C is naturally isomorphic to the functor from the
singleton category that maps to object x in Cᵒᵖ. *)
Section Func_From_SingletonCat_Opposite.
  Context {C : Category} (x : C).

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.
  
  Program Definition Func_From_SingletonCat_Opposite :
    (
      (((@Func_From_SingletonCat C x)^op)
         ≃ (@Func_From_SingletonCat (C ^op) x))%functor
    )%natiso
    :=
      {|
        iso_morphism :=
          {|
            Trans := fun _ => id
          |};
        inverse_morphism :=
          {|
            Trans := fun _ => id
          |}
      |}
  .
    
End Func_From_SingletonCat_Opposite.

Section Discr_Func_Arrow_Iso.
  Context {C D : Category} (arrmap : (Arrow (C^op)) → D).

  (** Let A be the discrete categoty of morphisms of Cᵒᵖ and B be the category
of morphisms of C. We show that Aᵒᵖ ≃ Bᵒᵖ. *)
  Definition Discr_Cat_ArrowOp_Discr_Cat_Arrow_Op :
    ((((Discr_Cat (Arrow (C^op)))^op)%category)
       ≃≃ ((Discr_Cat (Arrow C))^op)%category ::> Cat)%isomorphism
    :=
      Opposite_Cat_Iso (Discr_Cat_Iso ((Arrow_OP_Iso C)⁻¹))
  .

  Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

  (** Let A be the discrete categoty of morphisms of Cᵒᵖ and B be the category
of morphisms of C. Let, furthermore, U : B → D be a function we show that
((Discr_Func_op (fun x : B => U x^) ∘ M) ≃ (Discr_Func_op U). Where x^ is
mirrored version of x (from an arrow of C to an arrow of Cᵒᵖ) and M is
Discr_Cat_ArrowOp_Discr_Cat_Arrow_Op defined above.
*)
  Program Definition Discr_Func_Arrow_Iso :
    (
      (
        (Discr_Func_op (fun x : Arrow C => arrmap (Arrow_to_Arrow_OP C x)))
          ∘ (iso_morphism Discr_Cat_ArrowOp_Discr_Cat_Arrow_Op)
      )%functor
        ≃ ((@Discr_Func_op D (Arrow (C^op)) arrmap))%functor
    )%natiso
    :=
      {|
        iso_morphism :=
          {|
            Trans := fun c => id
          |};
        inverse_morphism :=
          {|
            Trans := fun c => id
          |}
      |}
  .
    
End Discr_Func_Arrow_Iso.

Local Hint Extern 1 =>
match goal with [z : Arrow (Discr_Cat _) |- _] => destruct z as [? ? []] end.

(** The fact that in discrete categories object type and arrow
    type are isomorphic. *)
Program Definition Discr_Hom_Iso (A : Type) :
  (A ≃≃ Arrow (Discr_Cat A) ::> Type_Cat)%isomorphism :=
  (Build_Isomorphism
     Type_Cat
     _
     _
     (fun a => (Build_Arrow (Discr_Cat A) _ _ (eq_refl a)))
     (fun a : (Arrow (Discr_Cat _)) => Orig a)
     _
     _
  ).

Section Discretize.
  Context {C D : Category} {F G : (C –≻ D)%functor} (N : (F –≻ G)%nattrans).

  (** Discretizes a natural transformation. That is, it forgets about the
      arrow maps of the functors and assumes the functors are just discrete
      functors, retaining the object maps of the functors. *)
  Program Definition Discretize :
    ((Discr_Func (F _o)%object) –≻ (Discr_Func (G _o)%object))%nattrans
    :=
    {|
      Trans := Trans N
    |}.
  
End Discretize.
