From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Topos.SubObject_Classifier.
From Categories Require Import Basic_Cons.Terminal Basic_Cons.PullBack.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Coq_Cats.Type_Cat.CCC Coq_Cats.Type_Cat.Morphisms.
From Categories Require Import
        PreSheaf.PreSheaf
        PreSheaf.Terminal
        PreSheaf.PullBack
        PreSheaf.Morphisms
.

Require Import Coq.Logic.ChoiceFacts.

Local Axiom ConstructiveIndefiniteDescription_Type :
  forall T : Type, ConstructiveIndefiniteDescription_on T.

Require Coq.Logic.ClassicalFacts.

Local Axiom PropExt : ClassicalFacts.prop_extensionality.


Section Sieve.
  Context {C : Category} (c : C).

  Local Open Scope morphism_scope.

  (** A sive on c (an object of C) is a set of morphisms h : x –≻ c
     that is closed under pre-composition. In other words, if h : x –≻ c
     is in the sieve and h' : y –≻ x is another morphism, we have (h ∘ h')
     is also in the sieve. *)
  Definition Sieve :=
    {S : ∀ (x : C) (h : x –≻ c), Prop |
     ∀ (x : C) (h : x –≻ c), S x h → ∀ (y : C) (h' : y –≻ x), S y (h ∘ h')
    }.

  (** The total sieve is the sieve that contains all morphism ending in c. *)
  Definition TotalSieve : Sieve :=
    exist
      (fun S : ∀ x : C, (x –≻ c) → Prop =>
         ∀ (x : C) (h : x –≻ c), S x h → ∀ (y : C) (h' : y –≻ x), S y (h ∘ h'))
      (fun _ _ => True)
      (fun _ _ _ _ _ => I)
  .

End Sieve.

(** The presheaf that maps each object to the set of its sieves. *)
Section Sieve_PreSheaf.
  Context (C : Category).

  Local Open Scope morphism_scope.

  Program Definition Sieve_PreSheaf : PreSheaf C :=
    {|
      FO := fun c => @Sieve C c;
      FA :=
        fun c c' h S =>
          exist _ (fun y (h' : y –≻ c') => (proj1_sig S) _ (h ∘ h')) _
    |}
  .

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    intros c c' h S x f H y g.
    rewrite assoc_sym.
    apply (proj2_sig S); trivial.
  Qed.

  Next Obligation.
  Proof.
    intros c.
    extensionality S.
    apply sig_proof_irrelevance.
    extensionality z.
    extensionality f.
    cbn in *; auto.
  Qed.

  Next Obligation.
  Proof.
    intros a b c f g.
    extensionality S.
    apply sig_proof_irrelevance.
    extensionality z.
    extensionality h.
    cbn in *.
    rewrite assoc; trivial.
  Qed.

  (** The true presheaf morphism. The presheaf morphism that maps
      each object to its total sieve. *)
  Program Definition True_PreSheaf_morphism :
    ((PSh_Term_PreSheaf C) –≻ Sieve_PreSheaf)%nattrans
    :=
      {|
        Trans := fun c _ => @TotalSieve C c
      |}.

  Local Hint Extern 1 => progress cbn.

  Next Obligation.
  Proof.
    intros c c' h.
    extensionality x.
    apply sig_proof_irrelevance.
    FunExt; cbn; trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply True_PreSheaf_morphism_obligation_1.
  Qed.

End Sieve_PreSheaf.

Section PShCat_char_morph.
  Context
    {C : Category}
    {F G : PreSheaf C}
    (N : @Monic (PShCat C) F G)
  .

  Local Obligation Tactic := idtac.

  (** The characteristic morphism of a presheaf morphism. *)
  Program Definition PShCat_char_morph : (G –≻ (Sieve_PreSheaf C))%nattrans :=
    {|
      Trans :=
        fun c x =>
          exist
            _
            (fun y h => ∃ u, Trans (mono_morphism N) y u = (G _a h)%morphism x)
            _
    |}
  .

  Next Obligation.
  Proof.
    intros c x y h [u H1] z g.
    cbn in *.
    exists ((F _a g)%morphism u).
    cbn_rewrite (F_compose G h g).
    cbn_rewrite (equal_f (Trans_com (mono_morphism N) g)).
    rewrite H1.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros c c' h.
    extensionality x.
    apply sig_proof_irrelevance.
    extensionality d.
    extensionality g.
    cbn in *.
    cbn_rewrite (F_compose G h g).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply PShCat_char_morph_obligation_2.
  Qed.

  Section PShCat_char_morph_forms_pullback_morph_ex.
    Context
      (p : PreSheaf C)
      (pm1 : (p –≻ G)%nattrans)
      (pm2 : (p –≻ PSh_Term_PreSheaf C)%nattrans)
      (H : (PShCat_char_morph ∘ pm1)%nattrans =
           (True_PreSheaf_morphism C ∘ pm2)%nattrans)
    .

        (** The map underlying PShCat_char_morph_forms_pullback_morph_ex. *)
    Definition PShCat_char_morph_forms_pullback_morph_ex_Trans
               (c : C)
               (x : (p _o c)%object)
      :
        (F _o c)%object
      :=
        proj1_sig
          (
            ConstructiveIndefiniteDescription_Type
              _
              _
              (
                match
                  eq_sym
                    (
                      f_equal
                        (
                          fun w : (p –≻ Sieve_PreSheaf C)%nattrans =>
                            proj1_sig (Trans w c x) c id
                        ) H
                    )
                  in _ = W return W
                with
                  eq_refl => I
                end
              )
          )
    .

    (** The presheaf morphism from a presheaf that is a candidate
pullback of the characteristic presheaf morphism of N and the true
presheaf morphism to F (the domain of the monomorphism N).
*)
    Program Definition PShCat_char_morph_forms_pullback_morph_ex :
      (p –≻ F)%nattrans
      :=
        {|
          Trans := PShCat_char_morph_forms_pullback_morph_ex_Trans
        |}.

    Next Obligation.
    Proof.
    intros c c' h.
    extensionality x.
    unfold PShCat_char_morph_forms_pullback_morph_ex_Trans.
    cbn in *.
    match goal with
      [|- proj1_sig ?A = (F _a h)%morphism (proj1_sig ?B)] =>
      destruct A as [y H2];
        destruct B as [z H3];
        cbn in *
    end.
    cbn_rewrite (F_id G) in H2 H3.
    cbn_rewrite (equal_f (Trans_com pm1 h)) in H2.
    apply (f_equal ((G _a)%morphism h)) in H3.
    cbn_rewrite <- (equal_f (Trans_com (mono_morphism N) h) z) in H3.
    rewrite <- H3 in H2.
    eapply (equal_f (PreSheaf_Monic_components_is_Monic
                       N c' (unit : Type) (fun _ => y)
                       (fun _ => (F _a h z)%morphism) _) tt).
    Unshelve.
    + auto.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply PShCat_char_morph_forms_pullback_morph_ex_obligation_1.
    Qed.

  End PShCat_char_morph_forms_pullback_morph_ex.

  Local Hint Extern 1 => match goal with
                          [|- context [(?F _a id)%morphism]] => rewrite (F_id F)
                        end.

  Local Hint Extern 1 => apply PropExt; intuition.

  Local Hint Extern 1 =>
  match goal with
    [ f : (?d –≻ ?c)%morphism,
          x : (?F _o)%object ?c |- ∃ _ : (?F _o)%object ?d, _] =>
    exists (F _a f x)%morphism
  end.

  Local Hint Extern 1 =>
  match goal with
    [|- context [Trans ?f _ ((?F _a)%morphism ?h _)]] =>
    cbn_rewrite (equal_f (Trans_com f h))
  end.

  Local Hint Extern 1 => apply sig_proof_irrelevance.

  Local Hint Extern 1 => progress cbn in *.

  Local Hint Extern 1 =>
  match goal with
    [|- context [proj1_sig ?A]] =>
    let x := fresh "x" in
    let H := fresh "H" in
    destruct A as [x H]; cbn;
    try rewrite H
  end
  .

  Local Hint Extern 1 => unfold PShCat_char_morph_forms_pullback_morph_ex_Trans.

  Local Hint Extern 1 => match goal with
                          [|- ?A = ?B :> unit] => try destruct A;
                            try destruct B; trivial; fail
                        end.

  Local Obligation Tactic := basic_simpl; auto 7.

  Program Definition PShCat_char_morph_forms_pullback :
    is_PullBack
      (mono_morphism N) (t_morph (PSh_Terminal C) F)
      PShCat_char_morph (True_PreSheaf_morphism C)
    :=
      {|
        is_pullback_morph_ex := PShCat_char_morph_forms_pullback_morph_ex
      |}
  .

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    intros p' pm1 pm2 H1 g h H2 _ H4 _.
    rewrite <- H4 in H2; clear H4.
    apply NatTrans_eq_simplify.
    extensionality x.
    extensionality y.
    assert (H2' := f_equal (fun w : (p' –≻ G)%nattrans => Trans w x y) H2);
      clear H2.
    cbn in*.
    match goal with
      [|- ?A = ?B] =>
      eapply
        (
          equal_f
            (PreSheaf_Monic_components_is_Monic
               N
               x
               (unit : Type)
               (fun _ => A)
               (fun _ => B) _)
            tt
        )
    end.
    Unshelve.
    auto.
  Qed.

End PShCat_char_morph.

(** Sieves as defined above  form the sub-object classifier for presheaves.
    With ⊤ mapping the the total sieve. *)
Section PShCat_char_morph_unique.
  Context
    {C : Category}
    {F G : PreSheaf C}
    (N : @Monic (PShCat C) F G)
    (M : (G –≻ (Sieve_PreSheaf C))%nattrans)
    (hpb : is_PullBack
      (mono_morphism N) (t_morph (PSh_Terminal C) F)
      M (True_PreSheaf_morphism C)
    ).

  Theorem PShCat_char_morph_unique : M = (PShCat_char_morph N).
  Proof.
    unfold PShCat_char_morph.
    apply NatTrans_eq_simplify.
    extensionality x.
    extensionality y.
    cbn in *.
    apply sig_proof_irrelevance.
    cbn.
    extensionality z.
    extensionality h.
    apply PropExt; split.
    {
      intros Hx.
      assert
        (H1 :=
           is_pullback_morph_ex_com_1
             hpb
             (PMCM_PreSheaf_representing_d z unit)
             (PMCM_PreSheaf_morph_of_function
                z unit (fun _ => (G _a)%morphism h y))
             (
               @PMCM_PreSheaf_morph_of_function
                 C
                 (PSh_Term_PreSheaf C)
                 z
                 unit
                 (fun _ => tt)
             )
        ).
      match type of H1 with
        ∀ _ : ?A, _ =>
        cut (A);
          [intros H2;
            assert (H3 :=
                      f_equal
                        (fun w : (PMCM_PreSheaf_representing_d
                                  z unit –≻ G)%nattrans =>
                           Trans w z (id, tt))
                        (H1 H2)
                   )
          |]
      end.
      {
        cbn in H3.
        match type of H3 with
          Trans (mono_morphism N) _ ?A = ?B => exists A
        end.
        rewrite H3.
        cbn_rewrite (F_id G); trivial.
      }
      {
        clear H1.
        apply NatTrans_eq_simplify.
        extensionality w.
        extensionality v.
        cbn in *.
        cbn_rewrite (equal_f (Trans_com M (fst v)) ((G _a)%morphism h y)).
        apply sig_proof_irrelevance.
        cbn.
        extensionality d.
        extensionality u.
        cbn_rewrite (equal_f (Trans_com M h) y).
        cbn.
        apply PropExt; split; intros _; trivial.
        apply (proj2_sig (Trans M x y) z h Hx d ((fst v) ∘ u)%morphism).
      }
    }
    {
      intros [v Hv].
      assert (proj1_sig (Trans M z (Trans (mono_morphism N) z v)) z id).
      {
        exact
          (
            match
              eq_sym
                (
                  f_equal
                    (fun w : (F –≻ Sieve_PreSheaf C)%nattrans =>
                       proj1_sig (Trans w z v) z id)
                    (is_pullback_morph_com hpb)
                )
              in _ = u return u
            with
              eq_refl => I
            end
          ).
      }
      {
        rewrite Hv in H.
        cbn_rewrite (equal_f (Trans_com M h) y) in H.
        cbn in H.
        auto.
      }
    }
  Qed.

End PShCat_char_morph_unique.

Program Definition PSh_SubObject_Classifier (C : Category) :
  SubObject_Classifier (PShCat C) :=
  {|
    SOC := (Sieve_PreSheaf C);
    SOC_morph := (True_PreSheaf_morphism C :
                    ((terminal (PSh_Terminal C)) –≻ _)%nattrans);
    SOC_char := @PShCat_char_morph C;
    SO_pulback := @PShCat_char_morph_forms_pullback C
  |}.

Local Obligation Tactic := idtac.

Next Obligation.
Proof.
  intros C a b m h h' pb1 pb2.
  transitivity (PShCat_char_morph m).
  + apply PShCat_char_morph_unique; trivial.
  + symmetry.
    apply PShCat_char_morph_unique; trivial.
Qed.
