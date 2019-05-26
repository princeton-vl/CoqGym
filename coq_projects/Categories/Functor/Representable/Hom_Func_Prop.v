From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Functor.Representable.Hom_Func.
From Categories Require Import Cat.Cat Cat.Cat_Iso.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat NatTrans.NatIso.

Local Open Scope functor_scope.

Section Hom_Func_Twist.
  Context (C : Category).

  (** (Hom_Func Cᵒᵖ) = (Hom_Func C) ∘ (Twist_Func C Cᵒᵖ)
       Note that:
         (Home_Func C) : Cᵒᵖ×C -> Type_Cat 
       and
         (Twist_Func C Cᵒᵖ) : C×Cᵒᴾ → Cᵒᵖ×C
   *)
  Theorem Hom_Func_Twist : (Hom_Func (C^op)) = (Hom_Func C) ∘ (Twist_Func C (C^op)).
  Proof.
    Func_eq_simpl; cbn; auto.
  Qed.

End Hom_Func_Twist.



Section Prod_Func_Hom_Func_NT.
  Context {A B C D : Category}
          {F : A –≻ C^op}
          {F' : A –≻ D^op}
          {G : B –≻ C}
          {G' : B –≻ D}
          (N : (((Hom_Func C) ∘ (Prod_Functor F G))
                –≻ ((Hom_Func D) ∘ (Prod_Functor F' G')))%nattrans
          )
  .

  Local Obligation Tactic := idtac.
  
  (** Given a natural transformation from ((Hom_Func C) ∘ (Prod_Functor F G)) to
      ((Hom_Func D) ∘ (Prod_Functor F' G')), we construct a natural transformation
      from ((Hom_Func C^op) ∘ (Prod_Functor G F)) to 
      ((Hom_Func D^op) ∘ (Prod_Functor G' F')). *)
  Program Definition Prod_Func_Hom_Func_NT :
    (((Hom_Func (C^op)) ∘ (Prod_Functor G F))
       –≻ ((Hom_Func (D^op)) ∘ (Prod_Functor G' F')))%nattrans :=
    {|
      Trans := fun c h => Trans N (snd c, fst c) h
    |}.

  Next Obligation.
  Proof.
    intros [c1 c2] [c1' c2'] [h1 h2].
    extensionality x; cbn.
    repeat rewrite assoc_sym.
    exact (equal_f (@Trans_com _ _ _ _ N (c2, c1) (c2', c1') (h2, h1)) x).
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Prod_Func_Hom_Func_NT_obligation_1.
  Qed.

End Prod_Func_Hom_Func_NT.
  
Section Prod_Func_Hom_Func.
  Context {A B C D : Category}
          {F : A –≻ C^op}
          {F' : A –≻ D^op}
          {G : B –≻ C}
          {G' : B –≻ D}
          (N : (
                 ((Hom_Func C) ∘ (Prod_Functor F G))%functor
                   ≃ ((Hom_Func D) ∘ (Prod_Functor F' G'))%functor
               )%natiso
          )
  .
  
  Local Ltac TRC :=
  match goal with
    [|- ?W = _] =>
    match W with
      Trans ?A ?X (Trans ?B ?X ?Z) =>
      change W with (Trans (NatTrans_compose B A) X Z)
    end
  end.

  Local Obligation Tactic :=
    apply NatTrans_eq_simplify; FunExt; basic_simpl; TRC;
    solve [(cbn_rewrite (right_inverse N); trivial) |
           (cbn_rewrite (left_inverse N); trivial)].

  (** 
Given a natural isomorphism 
  ((Hom_Func C) ∘ (Prod_Functor F G)) ≃ ((Hom_Func D) ∘ (Prod_Functor F' G')),
we construct a natural ismorphism 
  ((Hom_Func C^op) ∘ (Prod_Functor G F)) ≃
   ((Hom_Func D^op) ∘ (Prod_Functor G' F'))
*)
  Program Definition Prod_Func_Hom_Func :
    ((((Hom_Func (C^op)) ∘ (Prod_Functor G F))%functor)
       ≃ ((Hom_Func (D^op)) ∘ (Prod_Functor G' F'))%functor)%natiso
    :=
      {|
        iso_morphism := Prod_Func_Hom_Func_NT (iso_morphism N);
        inverse_morphism := Prod_Func_Hom_Func_NT (inverse_morphism N)
      |}
  .
  
End Prod_Func_Hom_Func.

Section Prod_Func_Hom_Func_invl.
  Context {A B C D : Category}
          {F : A –≻ C^op}
          {F' : A –≻ D^op}
          {G : B –≻ C}
          {G' : B –≻ D}
          (N :
             (
               ((Hom_Func C) ∘ (Prod_Functor F G))%functor
                 ≃ ((Hom_Func D) ∘ (Prod_Functor F' G'))%functor
             )%natiso
          )
  .

  (** Prod_Func_Hom_Func defined above is involutive. *)
  Theorem Prod_Func_Hom_Func_invl :
    N = Prod_Func_Hom_Func (Prod_Func_Hom_Func N).
  Proof.
    apply Isomorphism_eq_simplify;
    apply NatTrans_eq_simplify; extensionality x; trivial.
  Qed.    

End Prod_Func_Hom_Func_invl.

(** If I : C ≃ D is an isomorphism of categories, then hom-functor of C is
    naturally isomorphic to hom-functor of D taken after conversion from C
    to D through I. In this section we prove this by providing both sides
    of natural isomorphism and showing that they are inverses. *)
Section Hom_Func_to_Iso_Hom_Func.
  Context {C D : Category} (I : (C ≃≃ D ::> Cat)%isomorphism).

  Local Obligation Tactic := idtac.
  
  Program Definition Hom_Func_to_Iso_Hom_Func :
    (
      (Hom_Func C)
        –≻ ((Hom_Func D)
              ∘
              (Prod_Functor ((iso_morphism I)^op) (iso_morphism I)))
    )%nattrans :=
    {|
      Trans := fun c h => ((iso_morphism I) _a h)%morphism
    |}.

  Next Obligation.
  Proof.
    basic_simpl; auto.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Hom_Func_to_Iso_Hom_Func_obligation_1.
  Qed.

  Program Definition Iso_Hom_Func_to_Hom_Func :
    (((Hom_Func D) ∘ (Prod_Functor ((iso_morphism I)^op) (iso_morphism I)))
       –≻ (Hom_Func C))%nattrans
    :=
    {|
      Trans := fun c h => Cat_Iso_conv_inv I ((inverse_morphism I) _a h)
    |}.

  Next Obligation.
  Proof.
    basic_simpl; FunExt.
    repeat rewrite F_compose.
    repeat rewrite Cat_Iso_conv_inv_compose.
    repeat rewrite Cat_Iso_conv_inv_I_inv_I; trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Iso_Hom_Func_to_Hom_Func_obligation_1.
  Qed.

    
  Program Definition Hom_Func_Cat_Iso :
    (
      (Hom_Func C)
        ≃ ((Hom_Func D)
             ∘ (Prod_Functor ((iso_morphism I)^op) (iso_morphism I)))%functor
    )%natiso :=
    {|
      iso_morphism := Hom_Func_to_Iso_Hom_Func;
      inverse_morphism := Iso_Hom_Func_to_Hom_Func
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; basic_simpl; FunExt.
    apply Cat_Iso_conv_inv_I_inv_I.
  Qed.    

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c; cbn.
    extensionality f.
    destruct (Cat_Iso_inv I f) as [g H].
    rewrite H.
    rewrite Cat_Iso_conv_inv_I_inv_I; trivial.
  Qed.
  
End Hom_Func_to_Iso_Hom_Func.
