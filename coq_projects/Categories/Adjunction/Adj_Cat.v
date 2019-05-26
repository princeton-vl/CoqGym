From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Adjunction.Adjunction Adjunction.Duality.
From Categories Require Import NatTrans.NatTrans.

Local Open Scope functor_scope.
(** Adjunctions form a category Adj where objects are categories and an arrow 
    from C to D is a pair of adjoint funtors F : C → D : G. *)
Section Adjunct_Id.
  Context (C : Category).

  Program Definition Adjunct_Id : (Functor_id C) ⊣ (Functor_id C) :=
    {|
      adj_unit := NatTrans_id _
    |}.

End Adjunct_Id.
  
Section Adjunct_Compose.
  Context {C D E : Category}
          {F : C –≻ D} {G : D –≻ C} (adj : F ⊣ G)
          {F' : D –≻ E} {G' : E –≻ D} (adj' : F' ⊣ G').
  
  Program Definition Adjunct_Compose : ((F' ∘ F) ⊣ (G ∘ G')) :=
    {|
      adj_unit :=
        {|Trans := fun c => (G _a ((Trans (adj_unit adj') (F _o c)))
                            ∘ (Trans (adj_unit adj) c))%morphism |};
      adj_morph_ex := fun _ _ f => adj_morph_ex adj' (adj_morph_ex adj f)
    |}.

  Next Obligation.
  Proof.
    rewrite assoc.
    set (W := (Trans_com (adj_unit adj) h)); cbn in W; rewrite W; clear W.
    rewrite assoc_sym.
    set (W := f_equal (G _a)%morphism
                      (Trans_com (adj_unit adj') ((F _a) h)%morphism));
      cbn in W; rewrite F_compose in W; rewrite W.
    repeat rewrite F_compose.
    auto.
  Qed.    

  Next Obligation.
  Proof.
    symmetry.
    apply Adjunct_Compose_obligation_1.
  Qed.    

  Next Obligation.
  Proof.
    rewrite assoc_sym.
    set (W := f_equal (G _a)%morphism
                      (adj_morph_com adj' (adj_morph_ex adj f)));
      rewrite F_compose in W; cbn in W; rewrite <- W; clear W.
    apply (adj_morph_com adj f).
  Qed.    

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros c d f g h H1 H2.
    cbn in *.
    rewrite assoc_sym in H1, H2.
    rewrite <- F_compose in H1, H2.
    set (W := @adj_morph_unique _ _ _ _ adj _ _ f _ _ H1 H2).
    cbn in W.
    match type of W with
      ?A = ?B =>
      apply (@adj_morph_unique _ _ _ _ adj' _ _ A _ _ eq_refl W)
    end.
  Qed.

End Adjunct_Compose.

Section Adjunct_Compose_assoc.
  Context {B C D E : Category}
          {F : B –≻ C} {G : C –≻ B} (adj : F ⊣ G)
          {F' : C –≻ D} {G' : D –≻ C} (adj' : F' ⊣ G')
          {F'' : D –≻ E} {G'' : E –≻ D} (adj'' : F'' ⊣ G'').
  
  Theorem Adjunct_Compose_assoc :
    match (Functor_assoc F F' F'') in _ = Y return Adjunct Y _ with
      eq_refl =>
      match eq_sym (Functor_assoc G'' G' G) in _ = Y return Adjunct _ Y with
        eq_refl =>
        Adjunct_Compose adj (Adjunct_Compose adj' adj'')
      end
    end
    = Adjunct_Compose (Adjunct_Compose adj adj') adj''.
  Proof.
    apply Adjunct_eq_simplify.
    {
      apply NatTrans_eq_simplify.
      extensionality x.
      apply JMeq_eq.
      destruct (Functor_assoc F F' F'').
      destruct (eq_sym (Functor_assoc G'' G' G)).
      cbn.
      rewrite F_compose.
      repeat rewrite assoc_sym.
      trivial.
    }
    {
      extensionality x.
      extensionality y.
      apply JMeq_eq.
      destruct (Functor_assoc F F' F'').
      destruct (eq_sym (Functor_assoc G'' G' G)).
      trivial.
    }
  Qed.

End Adjunct_Compose_assoc.

Section Adjunct_Id_unit_left.
  Context {B C: Category}
          {F : B –≻ C} {G : C –≻ B} (adj : F ⊣ G).
  
  Theorem Adjunct_Id_unit_left :
    match (Functor_id_unit_left _ _ F) in _ = Y return Adjunct Y _ with
      eq_refl =>
      match (Functor_id_unit_right _ _ G) in _ = Y return Adjunct _ Y with
        eq_refl =>
        Adjunct_Compose adj (Adjunct_Id C)
      end
    end 
    = adj.
  Proof.
    apply Adjunct_eq_simplify.
    {
      apply NatTrans_eq_simplify.
      extensionality x.
      apply JMeq_eq.
      destruct (Functor_id_unit_left _ _ F).
      destruct (Functor_id_unit_right _ _ G).
      cbn.
      auto.
    }
    {
      extensionality x.
      extensionality y.
      apply JMeq_eq.
      destruct (Functor_id_unit_left _ _ F).
      destruct (Functor_id_unit_right _ _ G).
      trivial.
    }
  Qed.

End Adjunct_Id_unit_left.

Section Adjunct_Id_unit_right.
  Context {B C: Category}
          {F : B –≻ C} {G : C –≻ B} (adj : F ⊣ G).
  
  Theorem Adjunct_Id_unit_right :
    match (Functor_id_unit_right _ _ F) in _ = Y return Adjunct Y _ with
      eq_refl =>
      match (Functor_id_unit_left _ _ G) in _ = Y return Adjunct _ Y with
        eq_refl =>
        Adjunct_Compose (Adjunct_Id B) adj
      end
    end 
    = adj.
  Proof.
    apply Adjunct_eq_simplify.
    {
      apply NatTrans_eq_simplify.
      extensionality x.
      apply JMeq_eq.
      destruct (Functor_id_unit_right _ _ F).
      destruct (Functor_id_unit_left _ _ G).
      cbn.
      auto.
    }
    {
      extensionality x.
      extensionality y.
      apply JMeq_eq.
      destruct (Functor_id_unit_right _ _ F).
      destruct (Functor_id_unit_left _ _ G).
      trivial.
    }
  Qed.

End Adjunct_Id_unit_right.

Definition Adjunct_Between (C D : Category) : Type :=
  {F : (C –≻ D) * (D –≻ C) & (fst F) ⊣ (snd F)}
.

Definition Adjunct_Between_Id (C : Category) : Adjunct_Between C C :=
  existT _ (Functor_id C, Functor_id C) (Adjunct_Id C).
  
Section Adjunct_Between_Compose.
  Context {C D E : Category}
          (adj : Adjunct_Between C D)
          (adj' : Adjunct_Between D E).

  Definition Adjunct_Between_Compose : Adjunct_Between C E :=
    existT _
           ((fst (projT1 adj') ∘ (fst (projT1 adj))),
            ((snd (projT1 adj)) ∘ (snd (projT1 adj'))))
           (Adjunct_Compose (projT2 adj) (projT2 adj')).

End Adjunct_Between_Compose.

Theorem sigT_eq_simplify {A : Type} {P : A → Type} (s s' : sigT P)
        (H : projT1 s = projT1 s')
  : match H in _ = Y return P Y with
      eq_refl => projT2 s
    end = projT2 s' → s = s'.
Proof.
  intros H'.
  destruct s as [s Ps]; destruct s' as [s' Ps'].
  change (existT P s Ps)
  with (existT _ (projT1 (existT P s Ps)) (projT2 (existT P s Ps))).
  change (existT P s' Ps')
  with (existT _ (projT1 (existT P s' Ps')) (projT2 (existT P s' Ps'))).
  rewrite <- H'.
  clear H'.
  destruct H.
  trivial.
Qed.  
                      
Section Adjunct_Between_Compose_assoc.
  Context {B C D E : Category}
           (adj : Adjunct_Between B C)
           (adj' : Adjunct_Between C D)
           (adj'' : Adjunct_Between D E).
  
  Theorem Adjunct_Between_Compose_assoc :
    Adjunct_Between_Compose adj (Adjunct_Between_Compose adj' adj'') =
    Adjunct_Between_Compose (Adjunct_Between_Compose adj adj') adj''.
  Proof.
    destruct adj as [[F G] adjb]; destruct adj' as [[F' G'] adjb'];
    destruct adj'' as [[F'' G''] adjb''].
    set (W := Functor_assoc (fst (F, G)) (fst (F', G')) (fst (F'', G''))).
    set (W' := eq_sym (Functor_assoc
                         (snd (F'', G'')) (snd (F', G')) (snd (F, G)))).
    match type of W with
      ?A = ?B =>
      match type of W' with
        ?A' = ?B' =>
        match goal with
          [|- ?X = ?Z] =>
          set (H :=
                 match W in _ = Y return (A, _) = (Y, _) with
                   eq_refl =>
                   match W' in _ = Y return (_, A') = (_, Y) with
                     eq_refl => eq_refl (A, A')
                   end
                 end : projT1 X = projT1 Z)
        end
      end
    end.
    apply (sigT_eq_simplify _ _ H).
    etransitivity; [|apply Adjunct_Compose_assoc].
    unfold W, W' in H; clear W W'; unfold H; clear H.
    cbn.
    destruct (Functor_assoc F F' F'').
    destruct (eq_sym (Functor_assoc G'' G' G)).
    trivial.
  Qed.

End Adjunct_Between_Compose_assoc.

Section Adjunct_Between_Id_unit_left.
  Context {B C: Category}
          (adj : Adjunct_Between B C).
  
  Theorem Adjunct_Between_Id_unit_left :
    Adjunct_Between_Compose adj (Adjunct_Between_Id C) = adj.
  Proof.
    destruct adj as [[F G] adjb].
    set (W := (Functor_id_unit_left _ _ (fst (F, G)))).
    set (W' := (Functor_id_unit_right _ _ (snd (F, G)))).
    match type of W with
      ?A = ?B =>
      match type of W' with
        ?A' = ?B' =>
        match goal with
          [|- ?X = ?Z] =>
          set (H :=
                 match W in _ = Y return (A, _) = (Y, _) with
                   eq_refl =>
                   match W' in _ = Y return (_, A') = (_, Y) with
                     eq_refl => eq_refl (A, A')
                   end
                 end : projT1 X = projT1 Z)
        end
      end
    end.
    apply (sigT_eq_simplify _ _ H).
    match type of (@Adjunct_Id_unit_left _ _ _ _ adjb) with
      ?A = ?B => transitivity A; [|apply (@Adjunct_Id_unit_left _ _ _ _ adjb)]
    end.
    unfold W, W' in H; clear W W'; unfold H; clear H.
    cbn.
    destruct (Functor_id_unit_left _ _ F).
    destruct (Functor_id_unit_right _ _ G).
    trivial.
  Qed.

End Adjunct_Between_Id_unit_left.

Section Adjunct_Between_Id_unit_right.
  Context {B C: Category}
          (adj : Adjunct_Between B C).
  
  Theorem Adjunct_Between_Id_unit_right :
    Adjunct_Between_Compose (Adjunct_Between_Id B) adj = adj.
  Proof.
    destruct adj as [[F G] adjb].
    set (W := (Functor_id_unit_right _ _ (fst (F, G)))).
    set (W' := (Functor_id_unit_left _ _ (snd (F, G)))).
    match type of W with
      ?A = ?B =>
      match type of W' with
        ?A' = ?B' =>
        match goal with
          [|- ?X = ?Z] =>
          set (H :=
                 match W in _ = Y return (A, _) = (Y, _) with
                   eq_refl =>
                   match W' in _ = Y return (_, A') = (_, Y) with
                     eq_refl => eq_refl (A, A')
                   end
                 end : projT1 X = projT1 Z)
        end
      end
    end.
    apply (sigT_eq_simplify _ _ H).
    match type of (@Adjunct_Id_unit_right _ _ _ _ adjb) with
      ?A = ?B => transitivity A; [|apply (@Adjunct_Id_unit_right _ _ _ _ adjb)]
    end.
    unfold W, W' in H; clear W W'; unfold H; clear H.
    cbn.
    destruct (Functor_id_unit_right _ _ F).
    destruct (Functor_id_unit_left _ _ G).
    trivial.
  Qed.

End Adjunct_Between_Id_unit_right.

Definition Adjunct_Cat : Category :=
  {|
    Obj := Category;
    Hom := Adjunct_Between;
    compose := @Adjunct_Between_Compose;
    assoc := @Adjunct_Between_Compose_assoc;
    assoc_sym :=
      fun A B C D adj adj' adj'' =>
        eq_sym (@Adjunct_Between_Compose_assoc A B C D adj adj' adj'');
    id := Adjunct_Between_Id;
    id_unit_right := @Adjunct_Between_Id_unit_right;
    id_unit_left := @Adjunct_Between_Id_unit_left
  |}.
