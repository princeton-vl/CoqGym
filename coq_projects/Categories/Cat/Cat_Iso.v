From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.
From Categories Require Import Cat.Cat.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations NatTrans.Func_Cat
        NatTrans.NatIso.

Local Open Scope isomorphism_scope.
Local Open Scope morphism_scope.
Local Open Scope object_scope.

(** If two categories are isomorphic, then so are their duals. *)
Section Opposite_Cat_Iso.
  Context {C D : Category} (I : C ≃≃ D ::> Cat).

  Program Definition Opposite_Cat_Iso :
    (C^op)%category ≃≃ (D^op)%category ::> Cat
    :=
      {|
        iso_morphism := ((iso_morphism I)^op)%functor;
        inverse_morphism := ((inverse_morphism I)^op)%functor
      |}.

  Next Obligation.
    change (I ⁻¹ ^op ∘ (iso_morphism I) ^op)%functor
    with (((inverse_morphism I) ∘ (iso_morphism I))^op)%functor.
    cbn_rewrite (left_inverse I).
    trivial.
  Qed.

  Next Obligation.
    change ((iso_morphism I) ^op ∘ I ⁻¹ ^op)%functor
    with (((iso_morphism I) ∘ (inverse_morphism I))^op)%functor.
    cbn_rewrite (right_inverse I).
    trivial.
  Qed.

End Opposite_Cat_Iso.
  
(** Conversion from a category to another isomorphic category. *)
Section Cat_IConv.
  Context {C D : Category} (I : C ≃≃ D ::> Cat).

  (** Object conversion through an isomorphism and its inverse isomorphism
      gives back the same object. *)
  Definition Cat_Iso_Obj_conv (c : C) :
    c = (((inverse_morphism I) _o) (((iso_morphism I) _o) c))%object.
  Proof.
    change (I ⁻¹ _o ((iso_morphism I) _o c))
    with ((I ⁻¹ ∘ I)%morphism _o c)%object;
    rewrite (left_inverse I); trivial.
  Qed.

  (** Homomorphism types remain the smae after object conversion through an
      isomorphism and its inverse isomorphism. *)
  Definition Cat_Iso_Hom_conv (c c' : C) :
    ((((inverse_morphism I) _o) (((iso_morphism I) _o) c))
      –≻
      (((inverse_morphism I) _o) (((iso_morphism I) _o) c')))%morphism
    = (c –≻ c').
  Proof.
    do 2 rewrite <- Cat_Iso_Obj_conv; trivial.
  Defined.

  (** Type conversion to the original hom type after conversion with 
      an isomorphism and its inverse. *)
  Definition Cat_Iso_conv_inv {c c' : C}
             (h :
                (((inverse_morphism I) _o) (((iso_morphism I) _o) c))
                  –≻ (((inverse_morphism I) _o) (((iso_morphism I) _o) c')))
    : c –≻ c' :=
    match Cat_Iso_Hom_conv c c' in _ = Y return Y with
      eq_refl => h
    end.

  (** Heterogenous equality of type conversion to the original hom type after
      conversion with an isomorphism and its inverse. *)
  Theorem Cat_Iso_conv_inv_JMeq {c c' : C}
          (h :
             (((inverse_morphism I) _o) (((iso_morphism I) _o) c))
               –≻ (((inverse_morphism I) _o) (((iso_morphism I) _o) c')))
    : Cat_Iso_conv_inv h ~= h.
  Proof.
    unfold Cat_Iso_conv_inv.
    destruct Cat_Iso_Hom_conv.
    trivial.
  Qed.

  (** Type conversion to the original hom type after conversion with the
      inverse of an isomorphism and that isomorphism. *)
  Definition Cat_Iso_conv {c c' : C} (h : c –≻ c') :
    (((inverse_morphism I) _o) (((iso_morphism I) _o) c))
      –≻ (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))
    :=
    match eq_sym (Cat_Iso_Hom_conv c c') in _ = Y return Y with
      eq_refl => h
    end.
  
  (** Heterogenous equality of type conversion to the original hom type after
      conversion with the inverse of an isomorphism and that isomorphism. *)
  Theorem Cat_Iso_conv_JMeq {c c' : C} (h : c –≻ c') : Cat_Iso_conv h ~= h.
  Proof.
    unfold Cat_Iso_conv.
    destruct Cat_Iso_Hom_conv.
    trivial.
  Qed.

  (** Conversion once through an isomrphism and its inverse and once through
      its inverse and it gives back the same arrow as we strated with. *)
  Theorem Cat_Iso_conv_inv_Cat_Iso_conv {c c' : C} (h : c –≻ c')
    : Cat_Iso_conv_inv (Cat_Iso_conv h) = h.
  Proof.
    unfold Cat_Iso_conv_inv, Cat_Iso_conv.
    destruct Cat_Iso_Hom_conv; trivial.
  Qed.

  (** Conversion once through the inverse of an isomrphism and that isomorphism
      and once through that isomorphism and its inverse gives back the same
      arrow as we strated with. *)
  Theorem Cat_Iso_conv_Cat_Iso_conv_inv {c c' : C}
          (h :
             (((inverse_morphism I) _o) (((iso_morphism I) _o) c))
               –≻ (((inverse_morphism I) _o) (((iso_morphism I) _o) c')))
    :
      Cat_Iso_conv (Cat_Iso_conv_inv h) = h.
  Proof.
    unfold Cat_Iso_conv_inv, Cat_Iso_conv.
    destruct Cat_Iso_Hom_conv; trivial.
  Qed. 

  (** Conversion of an arrow through an isomorphism and its inverse (after
      correcting the homorphism type) is the same arrow as we started with. *)
  Theorem Cat_Iso_conv_inv_I_inv_I {c c' : C} (h : c –≻ c') :
    Cat_Iso_conv_inv (((inverse_morphism I) _a) (((iso_morphism I) _a) h)) = h.
  Proof.
    match goal with
      [|- ?A = ?B] =>
      let H := fresh "H" in
      cut (A ~= B); [intros H; rewrite H; trivial|]
    end.
    unfold Cat_Iso_conv_inv.
    destruct Cat_Iso_Hom_conv.
    change (I ⁻¹ _a ((iso_morphism I) _a h)) with ((I ⁻¹ ∘ I)%morphism _a h).
    apply (@JMeq_trans _ _ _ _ ((Functor_id _) _a h) _); trivial.
    cbn_rewrite <- (left_inverse I).
    trivial.
  Qed.

  (** Morphism composition commutes with conversion. *)
  Theorem Cat_Iso_conv_inv_compose {c c' c'' : C}
          (h :
             (((inverse_morphism I) _o) (((iso_morphism I) _o) c))
               –≻ (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))
          )
          (h' :
             (((inverse_morphism I) _o) (((iso_morphism I) _o) c'))
               –≻ (((inverse_morphism I) _o) (((iso_morphism I) _o) c''))
          )
    :
      Cat_Iso_conv_inv (compose C h h')
      = compose C (Cat_Iso_conv_inv h) (Cat_Iso_conv_inv h').
  Proof.
    unfold Cat_Iso_conv_inv, Cat_Iso_Hom_conv.
    do 3 destruct Cat_Iso_Obj_conv; trivial.
  Qed.

End Cat_IConv.

Section Cat_Iso_inv.
  Context {C D : Category} (I : C ≃≃ D ::> Cat).

  (** The main theorem of this module. Given an isomorphism I between
      categories C and D, for each morphism h: Hom (I _o c) (I _o c')
      in D, there is a morphism g in C such that the conversion of h
      through I (I _a g) gives back the smae arrow, i.e., h = (I _a h). *)
  Theorem Cat_Iso_inv
          {c c' : C} (h : ((iso_morphism I) _o c) –≻ ((iso_morphism I) _o c'))
    : {g : c –≻ c' | h = ((iso_morphism I) _a g)}.
  Proof.
    exists (Cat_Iso_conv_inv I ((inverse_morphism I) _a h)).
    match goal with
      [|- ?A = ?B] =>
        etransitivity;
        [apply (eq_sym (@Cat_Iso_conv_inv_I_inv_I D C (I⁻¹) _ _ A))|
         etransitivity; [|apply (@Cat_Iso_conv_inv_I_inv_I D C (I⁻¹) _ _ B)]]
    end.
    do 2 apply f_equal.
    match goal with
      [|- ?A = ?B] =>
        etransitivity;
        [apply (eq_sym (@Cat_Iso_conv_Cat_Iso_conv_inv C D I _ _ A))|
         etransitivity; [|apply (@Cat_Iso_conv_Cat_Iso_conv_inv C D I _ _ B)]]
    end.
    apply f_equal.
    rewrite Cat_Iso_conv_inv_I_inv_I; trivial.
  Qed.

End Cat_Iso_inv.

(**
Given I : C ≃ D for categories C and D and F : D -> E, F ∘ (I ∘ I⁻¹) and F are
naturally isomorphic.
*)
Section IsoCat_NatIso.
  Context {C D : Category} (I : (C ≃≃ D ::> Cat)%morphism)
          {E : Category} (F : (D –≻ E)%functor).

  Program Definition IsoCat_NatIso :
    ((F ∘ ((iso_morphism I) ∘ (I⁻¹)%morphism))%functor ≃ F)%natiso :=
    {|
      iso_morphism := IsoCat_NatTrans I F;
      inverse_morphism := IsoCat_NatTrans_back I F
    |}
  .

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    FunExt.
    cbn.
    match goal with
      [|- ((match ?e with _ => _ end) ∘ (match ?e with _ => _ end))%morphism = _] =>
      destruct e
    end.
    auto.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    FunExt.
    cbn.
    match goal with
      [|- ((match ?e with _ => _ end) ∘ (match ?e with _ => _ end))%morphism = _] =>
      destruct e
    end.
    auto.
  Qed.

End IsoCat_NatIso.
