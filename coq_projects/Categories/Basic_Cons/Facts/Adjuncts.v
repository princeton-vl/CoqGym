From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Basic_Cons.Product.
From Categories Require Import Basic_Cons.Exponential Basic_Cons.Exponential_Functor.
From Categories Require Import Adjunction.Adjunction.
From Categories Require Import Ext_Cons.Prod_Cat.Operations.
From Categories Require Import NatTrans.NatTrans.

(** Δ ⊣ × *)
Section Prod_Adj.
  Context (C : Category) (HP : Has_Products C).

  Hint Extern 1 =>
  eapply Prod_morph_unique;
    eauto;
    repeat rewrite assoc_sym;
    repeat rewrite Prod_morph_com_1;
    repeat rewrite Prod_morph_com_2;
    repeat rewrite assoc;
    repeat rewrite Prod_morph_com_1;
    repeat rewrite Prod_morph_com_2
  .
  
  Program Definition Prod_Adj : ((Diag_Func C) ⊣ (×ᶠⁿᶜ C HP))%functor :=
    {|
      adj_unit := {|Trans := fun c => @Prod_morph_ex _ _ _ (HP c c) c id id |};
      adj_morph_ex := fun c c' h => (Pi_1 ∘ h, Pi_2 ∘ h)%morphism
    |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros c d f [g1 g2] [h1 h2] H1 H2.
    cbn in *.
    replace g1 with (Pi_1 ∘ f)%morphism;
      [|rewrite H1; rewrite assoc_sym; rewrite Prod_morph_com_1;
        rewrite assoc; rewrite Prod_morph_com_1; auto].
    replace g2 with (Pi_2 ∘ f)%morphism;
      [|rewrite H1; rewrite assoc_sym; rewrite Prod_morph_com_2;
        rewrite assoc; rewrite Prod_morph_com_2; auto].
    replace h1 with (Pi_1 ∘ f)%morphism;
      [|rewrite H2; rewrite assoc_sym; rewrite Prod_morph_com_1;
        rewrite assoc; rewrite Prod_morph_com_1; auto].
    replace h2 with (Pi_2 ∘ f)%morphism;
      [|rewrite H2; rewrite assoc_sym; rewrite Prod_morph_com_2;
        rewrite assoc; rewrite Prod_morph_com_2; auto]; trivial.
  Qed.

End Prod_Adj.

(** + ⊣ Δ *)
Section Sum_Adj.
  Context (C : Category) (HS : Has_Sums C).

  Hint Extern 1 =>
  eapply Prod_morph_unique; eauto; repeat rewrite assoc_sym;
  repeat rewrite Prod_morph_com_1; repeat rewrite Prod_morph_com_2;
  repeat rewrite assoc; repeat rewrite Prod_morph_com_1;
  repeat rewrite Prod_morph_com_2.
  
  Program Definition Sum_Adj : ((+ᶠⁿᶜ C HS) ⊣ (Diag_Func C))%functor :=
    {|
      adj_unit :=
        {|
          Trans :=
            fun c =>
              (@Pi_1 _ _ _ (HS (fst c) (snd c)), @Pi_2 _ _ _ (HS (fst c) (snd c)))
        |};
      adj_morph_ex :=
        fun c c' h =>
          @Prod_morph_ex _ _ _ (HS (fst c) (snd c)) c' (fst h) (snd h)
    |}.

  Next Obligation.
  Proof.
    match goal with
      [|- (?A, ?B) = (?C, ?D)] => cutrewrite(C = A); [cutrewrite (D = B)|]; trivial
    end.
    apply (@Prod_morph_com_2 (C^op)).
    apply (@Prod_morph_com_1 (C^op)).
  Qed.

  Next Obligation.
  Proof.
    match goal with
      [|- (?A, ?B) = (?C, ?D)] => cutrewrite(A = C); [cutrewrite (B = D)|]; trivial
    end.
    apply (@Prod_morph_com_2 (C^op)).
    apply (@Prod_morph_com_1 (C^op)).
  Qed.

  Next Obligation.
  Proof.
    match goal with
      [|- (?A, ?B) = (?C, ?D)] => cutrewrite(C = A); [cutrewrite (D = B)|]; trivial
    end.
    apply (@Prod_morph_com_2 (C^op)).
    apply (@Prod_morph_com_1 (C^op)).
  Qed.    
  
  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros [c1 c2] d [f1 f2] g h H1 H2.
    cbn in *.
    apply (@Prod_morph_unique _ _ _ (HS c1 c2) d f1 f2); symmetry.
    apply (f_equal fst H1).
    apply (f_equal snd H1).
    apply (f_equal fst H2).
    apply (f_equal snd H2).
  Qed.

End Sum_Adj.

(** a × – ⊣ a⁻ *)
Section Prod_Exp_Adj.
  Context (C : Category) (HP : Has_Products C) (HE : Has_Exponentials C) (x : C).

  Program Definition Prod_Exp_Adj :
    (
      (Fix_Bi_Func_2 x (×ᶠⁿᶜ C HP)) ⊣ (@Fix_Bi_Func_1 (C^op) _ _ x (⇑ᶠⁿᶜ HE))
    )%functor
    :=
    {|
      adj_unit := {|Trans := fun c => Exp_morph_ex (HE x (HP c x)) c id|};
      adj_morph_ex := fun c c' h => uncurry _ h
    |}.

  Next Obligation.
  Proof.
    eapply Exp_morph_unique; eauto; cbn.
    set (M := curry_compose); unfold curry in M; cbn in M; rewrite M.
    cbn_rewrite <- (@Exp_morph_com C HP _ _ (HE x (HP c' x))).
    rewrite M.
    cbn_rewrite <- (@Exp_morph_com C HP _ _ (HE x (HP c' x))).
    replace
      (Prod_morph_ex
         (HP (HE x (HP c x)) x)
         (HP (HE x (HP c x)) x)
         (id ∘ Pi_1)
         (id ∘ Pi_2)
      )
    with (id (HP (HE x (HP c x)) x)).
    {
      repeat rewrite id_unit_right.
      rewrite assoc.
      rewrite <- (id_unit_left _ _ Pi_2).
      cbn_rewrite <- (@Exp_morph_com C HP _ _ (HE x (HP c x))).
      auto.
    }
    {
      eapply Prod_morph_unique; eauto;
      try rewrite Prod_morph_com_1;
      try rewrite Prod_morph_com_2;
      auto.
    }
  Qed.

  Next Obligation.
  Proof.  
    symmetry.
    apply Prod_Exp_Adj_obligation_1.
  Qed.

  Next Obligation.
  Proof.
    set (M := curry_compose); unfold curry in M; cbn in M; rewrite M.
    eapply Exp_morph_unique; eauto; cbn.
    cbn_rewrite <- (@Exp_morph_com C HP _ _ (HE x d)).
    replace (
        Prod_morph_ex
          (HP (HE x (HP c x)) x)
          (HP (HE x (HP c x)) x)
          (id ∘ Pi_1)
          (id ∘ Pi_2)
      )
    with (id (HP (HE x (HP c x)) x)).
    {
      repeat rewrite id_unit_right.
      repeat rewrite assoc.
      rewrite <- (id_unit_left _ _ Pi_2).
      cbn_rewrite <- (@Exp_morph_com C HP _ _ (HE x (HP c x))).
      unfold uncurry; cbn.
      auto.
    }
    {
      eapply Prod_morph_unique;
      eauto;
      try rewrite Prod_morph_com_1;
      try rewrite Prod_morph_com_2;
      auto.
    }
  Qed.    

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros c c' f g h H1 H2.
    rewrite H1 in H2; clear H1.
    cbn in *.
    replace (Prod_morph_ex
               (HP (HE x (HP c x)) x) (HP (HE x (HP c x)) x)
               (id ∘ Pi_1) (id ∘ Pi_2)) with (id (HP (HE x (HP c x)) x)) in H2.
    {
      rewrite id_unit_right in H2.
      set (M := curry_compose); unfold curry in M; cbn in M; rewrite M in H2.
      rewrite assoc in H2.
      rewrite <- (id_unit_left _ _ Pi_2) in H2.
      cbn_rewrite <- (@Exp_morph_com C HP) in H2.
      rewrite M in H2.
      rewrite assoc in H2.
      rewrite <- (id_unit_left _ _ Pi_2) in H2.
      cbn_rewrite <- (@Exp_morph_com C HP) in H2.
      simpl_ids in H2.
      eapply curry_injective.
      trivial.
    }    
    {
      eapply Prod_morph_unique;
      eauto;
      try rewrite Prod_morph_com_1;
      try rewrite Prod_morph_com_2;
      auto.
    }
  Qed.

End Prod_Exp_Adj.
