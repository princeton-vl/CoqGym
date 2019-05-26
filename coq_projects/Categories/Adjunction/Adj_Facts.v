From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Nat_Facts
        Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Functor.Main.
From Categories Require Import Functor.Representable.Hom_Func
        Functor.Representable.Hom_Func_Prop.
From Categories Require Import NatTrans.Main.
From Categories Require Import Adjunction.Adjunction Adjunction.Duality.
From Categories Require Import Cat.Cat Cat.Exponential Cat.Exponential_Facts.
From Categories Require Import Yoneda.Yoneda.
From Categories Require Import Functor.Functor_Extender.

Local Open Scope functor_scope.

Section Hom_Adjunct_left_iso.
  Context {C D : Category}
          {F F' : C –≻ D}
          (N : (F' ≃ F)%natiso)
          {G : D –≻ C}
          (adj : F ⊣_hom G)
  .


  (** If F ≃ F' and (F ⊣_hom G) then (F' ⊣_hom G) *)
  Definition Hom_Adjunct_left_iso : F' ⊣_hom G :=
    (adj ∘ ((NatTrans_id_Iso (Hom_Func D))
              ∘_h (Prod_Functor_NatIso
                     (N^op) (NatTrans_id_Iso (Functor_id D))))
    )%isomorphism%natiso.

End Hom_Adjunct_left_iso.

Section Hom_Adjunct_right_iso.
  Context {C D : Category}
          {F : C –≻ D}
          {G G' : D –≻ C}
          (N : (G ≃ G')%natiso)
          (adj : F ⊣_hom G)
  .

  (** If G ≃ G' and (F ⊣_hom G) then (F ⊣_hom G') *)
  Definition Hom_Adjunct_right_iso : F ⊣_hom G' :=
    Hom_Adjunct_Duality
      (Hom_Adjunct_left_iso
         ((N^op)⁻¹)%isomorphism%natiso (Hom_Adjunct_Duality adj)).

End Hom_Adjunct_right_iso.

Section Adjunct_left_iso.
  Context {C D : Category}
          (F F' : C –≻ D)
          (N : (F' ≃ F)%natiso)
          (G : D –≻ C)
          (adj : F ⊣ G)
  .

  (** If F ≃ F' and (F ⊣ G) then (F' ⊣ G) *)
  Definition Adjunct_left_iso : F' ⊣ G :=
    Hom_Adj_to_Adj (Hom_Adjunct_left_iso N (Adj_to_Hom_Adj adj)).

End Adjunct_left_iso.

Section Adjunct_right_iso.
  Context {C D : Category}
          (F : C –≻ D)
          (G G' : D –≻ C)
          (N : (G ≃ G')%natiso)
          (adj : F ⊣ G)
  .

  (** If G ≃ G' and (F ⊣ G) then (F ⊣ G') *)
  Definition Adjunct_right_iso : F ⊣ G' :=
    Hom_Adj_to_Adj (Hom_Adjunct_right_iso N (Adj_to_Hom_Adj adj)).

End Adjunct_right_iso.

Section Hom_Adjunct_left_unique.
  Context {C D : Category}
          {F F' : C –≻ D}
          {G : D –≻ C}
          (adj : F ⊣_hom G)
          (adj' : F' ⊣_hom G)
  .


  (** If F ⊣_hom G and F' ⊣_hom G then F ≃ F' *)
  Definition Hom_Adjunct_left_unique : (F ≃ F')%natiso.
  Proof.
    apply (@Opposite_NatIso _ _ (F^op) (F'^op)).
    eapply (Embedding_mono (Yoneda_Emb (D^op))).
    eapply Isomorphism_Compose;
      [eapply Inverse_Isomorphism; apply Exp_Cat_morph_ex_compose_Iso |].
    eapply Isomorphism_Compose; [|apply Exp_Cat_morph_ex_compose_Iso].
    apply Exp_Cat_morph_ex_Iso.
    eapply Isomorphism_Compose.
    apply adj.
    eapply Inverse_Isomorphism.
    apply adj'.
  Defined.

End Hom_Adjunct_left_unique.


Section Hom_Adjunct_right_unique.
  Context {C D : Category}
          {F : C –≻ D}
          {G G' : D –≻ C}
          (adj : F ⊣_hom G)
          (adj' : F ⊣_hom G')
  .

  (** If F ⊣_hom G and F ⊣_hom G' then G ≃ G' *)
  Theorem Hom_Adjunct_right_unique : (G ≃ G')%natiso.
  Proof.
    apply Hom_Adjunct_Duality in adj.
    apply Hom_Adjunct_Duality in adj'.
    apply (@Opposite_NatIso _ _ (G^op) (G'^op)).
    apply (Hom_Adjunct_left_unique adj adj').
  Defined.

End Hom_Adjunct_right_unique.

Section Adjunct_left_unique.
  Context {C D : Category}
          {F F' : C –≻ D}
          {G : D –≻ C}
          (adj : F ⊣ G)
          (adj' : F' ⊣ G)
  .

  (** If F ⊣ G and F' ⊣ G then F ≃ F' *)
  Theorem Adjunct_left_unique : (F ≃ F' )%natiso.
  Proof.
    apply Adj_to_Hom_Adj in adj.
    apply Adj_to_Hom_Adj in adj'.
    eapply Hom_Adjunct_left_unique; eassumption.
  Defined.

End Adjunct_left_unique.

Section Adjunct_right_unique.
  Context {C D : Category}
          {F : C –≻ D}
          {G G' : D –≻ C}
          (adj : F ⊣ G)
          (adj' : F ⊣ G')
  .

  (** If F ⊣ G and F ⊣ G' then G ≃ G' *)
  Theorem Adjunct_right_unique : (G ≃ G')%natiso.
  Proof.
    apply Adj_to_Hom_Adj in adj.
    apply Adj_to_Hom_Adj in adj'.
    eapply Hom_Adjunct_right_unique; eassumption.
  Defined.

End Adjunct_right_unique.

(** If F ⊣_ucu G then
    Hom_{Func_Cat B D}(Fᵒᵖ ∘ –, –) ≃ Hom_{Func_Cat B C}(–, G ∘ —) *)
Section Hom_Adjunct_Lifted.
  Context {C D : Category}
          {F : C –≻ D}
          {G : D –≻ C}
          (adj : F ⊣_ucu G)
          (B : Category)
  .

  Local Notation NID := NatTrans_id (only parsing).
  Local Notation FCAT := Func_Cat (only parsing).

  Local Notation LEFT :=
    (
      (Hom_Func (Func_Cat B D))
        ∘ (Prod_Functor
             ((Right_Functor_Extender F B)^op)
             (Functor_id (Func_Cat B D))
          )
    )
      (only parsing).

  Local Notation RIGHT :=
    (
      (Hom_Func (Func_Cat B C))
        ∘ (Prod_Functor
             (Functor_id ((Func_Cat B C)^op)%category)
             (Right_Functor_Extender G B)
          )
    )
      (only parsing).

  Local Obligation Tactic := idtac.
  
  Program Definition Hom_Adjunct_Lifted_LR : (LEFT –≻ RIGHT)%nattrans :=
    {|
      Trans := fun c h =>
                 ((((NatTrans_id G) ∘_h h)
                     ∘ ((NatTrans_Functor_assoc (fst c) F G)
                          ∘ ((ucu_adj_unit adj) ∘_h (NatTrans_id (fst c)))))
                    ∘ (NatTrans_to_compose_id _))%nattrans
    |}.

  Next Obligation.
    intros [c1 c2] [c1' c2'] [h1 h2].
    extensionality w.
    apply NatTrans_eq_simplify.
    extensionality x.
    cbn in *.
    repeat rewrite F_id; simpl_ids.
    repeat rewrite F_compose.
    repeat rewrite assoc.
    cbn_rewrite (@Trans_com _ _ _ _ (ucu_adj_unit adj) _ _ (Trans h1 x)).
    trivial.
  Qed.    

  Next Obligation.
    symmetry.
    apply Hom_Adjunct_Lifted_LR_obligation_1.
  Qed.

  Program Definition Hom_Adjunct_Lifted_RL : (RIGHT –≻ LEFT)%nattrans :=
    {|
      Trans := fun c h =>
                 ((NatTrans_from_compose_id _)
                    ∘ ((((ucu_adj_counit adj)
                           ∘_h (NatTrans_id (snd c)))
                          ∘ (NatTrans_Functor_assoc_sym (snd c) G F))
                         ∘ ((NatTrans_id F) ∘_h h)))%nattrans
    |}.
    
  Next Obligation.
    intros [c1 c2] [c1' c2'] [h1 h2].
    extensionality w.
    apply NatTrans_eq_simplify.
    extensionality x.
    cbn in *.
    repeat rewrite F_id; simpl_ids.
    repeat rewrite F_compose.
    repeat rewrite assoc_sym.
    cbn_rewrite (@Trans_com _ _ _ _ (ucu_adj_counit adj) _ _ (Trans h2 x)).
    trivial.
  Qed.    

  Next Obligation.
    symmetry.
    apply Hom_Adjunct_Lifted_RL_obligation_1.
  Qed.

  Program Definition Hom_Adjunct_Lifted : (LEFT ≃ RIGHT)%natiso :=
    {|
      iso_morphism := Hom_Adjunct_Lifted_LR;
      inverse_morphism := Hom_Adjunct_Lifted_RL
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify;
    extensionality c; extensionality h.
    destruct c as [c1 c2].
    apply NatTrans_eq_simplify; extensionality y.
    cbn in *.
    repeat rewrite F_id.
    simpl_ids.
    rewrite F_compose.
    rewrite assoc_sym.
    cbn_rewrite (Trans_com (ucu_adj_counit adj) (Trans h y)). 
    rewrite assoc.
    simpl_ids; trivial.
    set (W := f_equal (fun w => Trans w (c1 _o y)) (ucu_adj_left_id adj));
      cbn in W; simpl_ids in W; apply W.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify;
    extensionality c; extensionality h.
    destruct c as [c1 c2].
    apply NatTrans_eq_simplify; extensionality y.
    cbn in *.
    repeat rewrite F_id.
    simpl_ids.
    rewrite F_compose.
    rewrite assoc.
    cbn_rewrite <- (Trans_com (ucu_adj_unit adj) (Trans h y)).
    rewrite assoc_sym.
    simpl_ids; trivial.
    set (W := f_equal (fun w => Trans w (c2 _o y)) (ucu_adj_right_id adj));
      cbn in W;
      repeat rewrite F_compose in W; repeat rewrite F_id in W; simpl_ids in W;
      apply W.
  Qed.

End Hom_Adjunct_Lifted.
