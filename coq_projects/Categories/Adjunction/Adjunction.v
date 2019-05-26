From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Functor.Main.
From Categories Require Import Functor.Representable.Hom_Func
        Functor.Representable.Hom_Func_Prop.
From Categories Require Import NatTrans.Main.

Local Open Scope functor_scope.

(** Local notations for simplification. *)
Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

(** This module contains different definitions of adjunctions and
    their conversion. *)

(** The left hand side of the isomorphism for adjunctions defined
    through hom functor. *)
Notation Hom_Adj_Left C D F G :=
  ((Hom_Func D) ∘ (Prod_Functor (F^op) (@Functor_id D)))%functor (only parsing).

(* The right hand side of the isomorphism for adjunctions defined
   through hom functor. *)
Notation Hom_Adj_Right C D F G :=
  ((Hom_Func C) ∘ (Prod_Functor (@Functor_id (C^op)) G))%functor (only parsing).

Local Obligation Tactic := idtac.

Section Adjunction.
  Context {C D : Category} (F : C –≻ D) (G : D –≻ C).

  (** This is the definition of adjunctions taken as them main definition in
      this development.  Functor F : C -> D is the left adjoint to functor
      G : D -> C if there is a natural transformation
      η : (Functor_id C) -> (G ∘ F) and for any arrow f : c -> (G _o d)
      there is a unique arrow
      f̂f^: (F _o c) d such that the following diagram commutes:

#
<pre>

              f
         c —————————–> (G _o d)
         |               ↗
         |             /
     η_c |           /  G _a  f^
         |         /
         ↓       /
   (G _o (F _o c))

</pre>
#
*)
  Record Adjunct : Type :=
  {
    adj_unit : ((Functor_id C) –≻ (G ∘ F))%nattrans;
    
    adj_morph_ex {c : C} {d : D} (f : (c –≻ (G _o d)%object)%morphism) :
      ((F _o c)%object –≻ d)%morphism;
    
    adj_morph_com {c : C} {d : D} (f : (c –≻ (G _o d))%morphism%object) :
      f = ((G _a (adj_morph_ex f)) ∘ (Trans adj_unit c))%morphism;
    
    adj_morph_unique {c : C} {d : D} (f : (c –≻ (G _o d))%object%morphism)
                     (g h : ((F _o c) –≻ d)%morphism%object) :
      f = ((G _a g) ∘ (Trans adj_unit c))%morphism →
      f = ((G _a h) ∘ (Trans adj_unit c))%morphism →
      g = h
  }.

  Arguments adj_unit : clear implicits.
  Arguments adj_morph_ex _ {_ _} _.
  Arguments adj_morph_com _ {_ _} _.
  Arguments adj_morph_unique _ {_ _} _ _ _ _ _.

  Theorem Adjunct_eq_simplify (adj adj' : Adjunct) :
    adj_unit adj = @adj_unit adj' →
    @adj_morph_ex adj = @adj_morph_ex adj' → adj = adj'.
  Proof.
    destruct adj; destruct adj'; basic_simpl.
    ElimEq.
    PIR.
    reflexivity.
  Qed.

  (** The hom functor definition of adjunction. F : C -> D is the left adjoint
       to G : D -> C if Hom_D(Fᵒᵖ, –) ≃ Hom_C(–, G)
*)  
  Definition Hom_Adjunct :=
    (Hom_Adj_Left _ _ F G ≃ Hom_Adj_Right _ _ F G)%natiso.

  
  (** The unit-counit definition of adjunctions. F : C -> D is the left adjoint
      to G : D -> C if there are two natural transformations
      η : (Functor_id C) -> (G ∘ F) and ε : (F ∘ G) -> (Functor_id D) such that
      we have the following two equalities hold:

     (ε ∘_h (NatTrans_id F)) ∘ ((NatTrans_id F) ∘_h η) = (NatTrans_id F)

     ((NatTrans_id FG) ∘_h ε) ∘ (η ∘_h (NatTrans_id G)) = (NatTrans_id G)

     In practice, we have compose some other natural transformations within
     the above equalities to correct the types. Therefore, we have:
*)
  Record UCU_Adjunct :=
    {
      ucu_adj_unit : ((Functor_id C) –≻ (G ∘ F))%nattrans;
      
      ucu_adj_counit : ((F ∘ G) –≻ (Functor_id D))%nattrans;

      ucu_adj_left_id : ((NatTrans_from_compose_id _)
                           ∘ ((((ucu_adj_counit ∘_h (NID F))
                                  ∘ (NatTrans_Functor_assoc_sym _ _ _))
                                 ∘ ((NID F) ∘_h ucu_adj_unit))
                                ∘ (NatTrans_to_id_compose _)))%nattrans
                        = (NID F);
      
      ucu_adj_right_id : ((NatTrans_from_id_compose _)
                            ∘ (((((NID G) ∘_h ucu_adj_counit)
                                   ∘ (NatTrans_Functor_assoc _ _ _))
                                  ∘ (ucu_adj_unit ∘_h (NID G)))
                                 ∘ (NatTrans_to_compose_id _)))%nattrans
                         = (NID G)
    }.

  Arguments ucu_adj_unit : clear implicits.
  Arguments ucu_adj_counit : clear implicits.
  Arguments ucu_adj_left_id : clear implicits.
  Arguments ucu_adj_right_id : clear implicits.

  Local Notation "F ⊣ G" := (Adjunct) : functor_scope.
  Local Notation "F ⊣_hom G" := (Hom_Adjunct) : functor_scope.
  Local Notation "F ⊣_ucu G" := (UCU_Adjunct) : functor_scope.
  
  Section UCU_Adj_Adj.
    Context (Adj : (F ⊣_ucu G)%functor).

    (** Conversion from unit-counit adjunction to adjunction. *)
    Program Definition UCU_Adj_to_Adj : (F ⊣ G)%functor :=
      {|
        adj_unit := ucu_adj_unit Adj;
        adj_morph_ex :=
          fun _ _ h => ((Trans (ucu_adj_counit Adj) _) ∘ (F _a h))%morphism
      |}.

    Next Obligation.
    Proof.
      intros c d f; cbn.
      rewrite F_compose; rewrite assoc.
      cbn_rewrite <- (Trans_com (ucu_adj_unit Adj) f).
      rewrite assoc_sym.
      set (W := f_equal (fun w => Trans w d) (ucu_adj_right_id Adj));
        cbn in W; repeat rewrite F_id in W; simpl_ids in W; rewrite W.
      auto.
    Qed.      

    Next Obligation.
    Proof.
      intros c d f g h H1 H2; cbn in *.
      rewrite H1 in H2; clear H1.
      apply (f_equal (F _a)%morphism) in H2.
      do 2 rewrite F_compose in H2.
      apply (f_equal (fun w => compose w (Trans (ucu_adj_counit Adj) _))) in H2;
        cbn in H2.
      repeat rewrite assoc_sym in H2.
     cbn_rewrite (@Trans_com _ _ _ _ (ucu_adj_counit Adj) _ _ g) in H2.
      cbn_rewrite (@Trans_com _ _ _ _ (ucu_adj_counit Adj) _ _ h) in H2.
      repeat rewrite assoc in H2.
      set (W := f_equal (fun w => Trans w c) (ucu_adj_left_id Adj));
        cbn in W; repeat rewrite F_id in W; simpl_ids in W; rewrite W in H2;
        clear W.
      auto.
    Qed.

  End UCU_Adj_Adj.

  Section Adj_UCU_Adj.
    Context (Adj : (F ⊣ G)%functor).
    
    (** Conversion from adjunction to unit-counit adjunction. *)
    Program Definition Adj_to_UCU_Adj : (F ⊣_ucu G)%functor :=
      {|
        ucu_adj_unit := adj_unit Adj;
        ucu_adj_counit :=
          {|
            Trans := fun d => @adj_morph_ex Adj (G _o d) d id
          |}
      |}.

    Next Obligation.
    Proof.    
      intros d d' h; cbn.
      eapply (@adj_morph_unique Adj); [reflexivity|]; cbn.
      repeat rewrite F_compose.
      repeat rewrite assoc.
      cbn_rewrite <- (@Trans_com _ _ _ _ (adj_unit Adj) _ _ ((G @_a) d d' h)).
      cbn_rewrite <- (@adj_morph_com Adj (G _o d) d id).
      rewrite assoc_sym.
      cbn_rewrite <- (@adj_morph_com Adj (G _o d') d' id).
      auto.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Adj_to_UCU_Adj_obligation_1.
    Qed.      

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality x.
      cbn; simpl_ids.
      eapply (@adj_morph_unique Adj); [reflexivity|]; cbn.
      rewrite F_compose.
      rewrite F_id.
      rewrite assoc.
      cbn_rewrite <- (@Trans_com
                       _ _ _ _ (adj_unit Adj) _ _ (Trans (adj_unit Adj) x)). 
      rewrite assoc_sym.
      simpl_ids; trivial.
      symmetry.
      apply adj_morph_com.
    Qed.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; FunExt; cbn.
      repeat rewrite F_id; simpl_ids.
      symmetry.
      apply adj_morph_com.
    Qed.

  End Adj_UCU_Adj.
  
  Section Adj_Hom_Adj.
    Context (Adj : (F ⊣ G)%functor).

    (** Conversion from adjunction to hom functor adjunction – the left to right
        natural transformation. *)
    Program Definition Adj_to_Hom_Adj_LR :
      ((Hom_Adj_Left _ _ F G) –≻ (Hom_Adj_Right _ _ F G))%nattrans :=
    {|
      Trans := fun c h => ((G _a h) ∘ (Trans (adj_unit Adj) _))%morphism
    |}.

    Next Obligation. (* Trans_com *)
      intros [c1 d1] [c2 d2] [h1 h2].
      extensionality x; cbn in *.
      repeat rewrite F_compose.
      change (G _a (F _a h1))%morphism with ((G ∘ F) _a h1)%morphism.
      repeat rewrite assoc.
      repeat refine (@f_equal _ _ (fun x => @compose _ _ _ _ x _) _ _ _).
      symmetry.
      apply (Trans_com (adj_unit Adj)). 
    Qed.

    Next Obligation. (* Trans_com *)
    Proof.
      symmetry.
      apply Adj_to_Hom_Adj_LR_obligation_1.
    Qed.

    (** Conversion from adjunction to hom functor adjunction – the right to left
        natural transformation. *)
    Program Definition Adj_to_Hom_Adj_RL :
      ((Hom_Adj_Right _ _ F G) –≻ (Hom_Adj_Left _ _ F G))%nattrans :=
    {|
      Trans := fun c h => adj_morph_ex Adj h
    |}.

    Next Obligation.
      intros [c1 d1] [c2 d2] [h1 h2].
      extensionality x; cbn in *.
      eapply adj_morph_unique; eauto.
      simpl_ids.
      rewrite <- adj_morph_com.
      repeat rewrite F_compose.
      repeat rewrite assoc.
      refine (@f_equal _ _ (fun x => @compose _ _ _ _ x _) _ _ _).
      change (G _a (F _a h1))%morphism with ((G ∘ F) _a h1)%morphism.
      refine (eq_trans _ (@f_equal
                            _ _ (fun x => @compose _ _ _ _ x _)
                            _ _ (Trans_com (adj_unit Adj) h1))).
      rewrite assoc_sym.
      rewrite <- adj_morph_com; trivial.
    Qed.

    Next Obligation. (* Trans_com *)
    Proof.
      symmetry.
      apply Adj_to_Hom_Adj_RL_obligation_1.
    Qed.

    (** Conversion from adjunction to hom functor adjunction. *)
    Program Definition Adj_to_Hom_Adj : (F ⊣_hom G)%functor :=
      NatIso _ _ Adj_to_Hom_Adj_LR Adj_to_Hom_Adj_RL _ _.
    
    Next Obligation.
      basic_simpl; FunExt.
      etransitivity; [symmetry; apply adj_morph_com| trivial].
    Qed.

    Next Obligation.
      basic_simpl; FunExt.
      eapply adj_morph_unique; eauto.
      rewrite <- adj_morph_com; trivial.
    Qed.

  End Adj_Hom_Adj.

  Section Hom_Adj_Adj.
    Context (Adj : (F ⊣_hom G)%functor).

    (** Conversion from hom functor adjunction to adjunction. *)
    Program Definition Hom_Adj_to_Adj : (F ⊣ G)%functor :=
      {|
        adj_unit :=
          {| Trans := fun c => Trans (iso_morphism Adj) (c, F _o c)%object id |};
        adj_morph_ex := fun _ _ f => Trans (inverse_morphism Adj) (_, _) f
      |}.
    
    Next Obligation.
      intros c c' h.
      set (H := @equal_f
                  _ _ _ _ (@Trans_com
                             _ _ _ _ (iso_morphism Adj) (c', F _o c')%object
                             (c, F _o c')%object (h, id)) id).
      set (H' := (@equal_f
                    _ _ _ _ (@Trans_com
                               _ _ _ _ (iso_morphism Adj) (c, F _o c)%object
                               (c, F _o c')%object (id c, F _a h)%morphism) id)
          ).
      cbn in *.
      rewrite F_id in H.
      rewrite F_id in H'.
      simpl_ids in H.
      simpl_ids in H'.
      rewrite <- H; trivial.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Hom_Adj_to_Adj_obligation_1.
    Qed.

    Next Obligation.
      intros c d f; cbn.
      set (H := @equal_f
                  _ _ _ _ (@Trans_com
                             _ _ _ _ (iso_morphism Adj)
                             (c, F _o c)%object (c, d)
                             (id, Trans (inverse_morphism Adj) (c, d) f)) id);
        cbn in H.
      rewrite F_id in H.
      simpl_ids in H.
      etransitivity; [|eassumption].
      change (f = Trans (NatTrans_compose
                           (inverse_morphism Adj) (iso_morphism Adj)) (_, _) f).
      set (H' := right_inverse Adj); cbn in H'.
      rewrite H'.
      cbn; auto.
    Qed.

    Next Obligation.
      intros c d f g h H1 H2.
      cbn in *.
      cut (Trans (NatTrans_compose
                    (iso_morphism Adj) (inverse_morphism Adj)) (_, _) g
           = Trans (NatTrans_compose
                      (iso_morphism Adj) (inverse_morphism Adj)) (_, _) h);
        [intros H'|].
      + set (H'' := left_inverse Adj); cbn in H''.
        rewrite H'' in H'.
        cbn in H'; auto.
      + set (Hg := @equal_f
                     _ _ _ _ (@Trans_com
                                _ _ _ _ (iso_morphism Adj) (c, F _o c)%object
                                (c, d) (id, g)) id); cbn in Hg;
        rewrite F_id in Hg; simpl_ids in Hg.
        set (Hh := @equal_f
                     _ _ _ _ (@Trans_com
                                _ _ _ _ (iso_morphism Adj) (c, F _o c)%object
                                (c, d) (id, h)) id); cbn in Hh;
        rewrite F_id in Hh; simpl_ids in Hh.
        cbn.
        rewrite Hg, Hh; rewrite <- H1, <- H2; trivial.
    Qed.        

  End Hom_Adj_Adj.

End Adjunction.

Arguments adj_unit {_ _ _ _} _ : assert.
Arguments adj_morph_ex {_ _ _ _} _ {_ _} _.
Arguments adj_morph_com {_ _ _ _} _ {_ _} _.
Arguments adj_morph_unique {_ _ _ _} _ {_ _} _ _ _ _ _.

Arguments ucu_adj_unit {_ _ _ _} _.
Arguments ucu_adj_counit {_ _ _ _} _.
Arguments ucu_adj_left_id {_ _ _ _} _.
Arguments ucu_adj_right_id {_ _ _ _} _.

Arguments Adj_to_Hom_Adj {_ _ _ _} _.

Arguments Hom_Adj_to_Adj {_ _ _ _} _.

Notation "F ⊣ G" := (Adjunct F G) : functor_scope.
Notation "F ⊣_hom G" := (Hom_Adjunct F G) : functor_scope.
Notation "F ⊣_ucu G" := (UCU_Adjunct F G) : functor_scope.
