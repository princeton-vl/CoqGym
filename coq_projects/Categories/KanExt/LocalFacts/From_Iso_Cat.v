From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations
        NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import KanExt.Local
        KanExt.LocalFacts.HomToCones
        KanExt.LocalFacts.ConesToHom
        KanExt.LocalFacts.Uniqueness.
From Categories Require Import Cat.Cat.

Local Open Scope functor_scope.

(** Given I : C ≃ D for C and D categories we have KanExt (p ∘ I) (F ∘ I) if
    we have KanExt p F. *)
Section KanExt_From_Isomorphic_Cat.
  Context {C D : Category}
          (I : (C ≃≃ D ::> Cat)%isomorphism)
          {D' : Category}
          (p : D –≻ D')
          {E : Category}
          (F : D –≻ E)
  .

  Section LoKan_Cone_Conv.
    Context (Cn : LoKan_Cone p F).
    
    Program Definition LoKan_Cone_Conv :
      LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))
      :=
        {|
          cone_apex := Cn;
          cone_edge :=
            (
              (
                (cone_edge Cn) ∘_h (NatTrans_id (iso_morphism I))
              )
                ∘ (NatTrans_Functor_assoc_sym _ _ _)
            )%nattrans
        |}
    .

  End LoKan_Cone_Conv.

  Section LoKan_Cone_Conv_back.
    Context (Cn : LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))).
    
    Program Definition LoKan_Cone_Conv_back :
      LoKan_Cone p F
      :=
        {|
          cone_apex := Cn;
          cone_edge :=
            (
              (IsoCat_NatTrans I F)
                ∘ (
                  (
                    (NatTrans_Functor_assoc _ _ _)
                      ∘ (
                        (Cn ∘ (NatTrans_Functor_assoc _ _ _))
                          ∘_h NatTrans_id (I ⁻¹)%morphism
                      )
                  )
                    ∘ (NatTrans_Functor_assoc_sym _ _ _)
                )
                ∘ IsoCat_NatTrans_back I (Cn ∘ p))%nattrans
        |}
    .
      
  End LoKan_Cone_Conv_back.

  Section LoKan_Cone_Moprh_to_Conv_back_and_forth.
    Context (Cn : LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))).
    
    Program Definition LoKan_Cone_Moprh_to_Conv_back_and_forth :
      LoKan_Cone_Morph Cn (LoKan_Cone_Conv (LoKan_Cone_Conv_back Cn))
      :=
        {|
          cone_morph := NatTrans_id Cn
        |}
    .

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality x.
      cbn.
      Functor_Simplify.
      simpl_ids.
      match goal with
        [|- _ = ((match ?e with _ => _ end)
                  ∘ _ ∘ (match ?e with _ => _ end))%morphism] =>
        generalize e
      end.
      intros e.
      set (z := ((I ⁻¹ _o) (((iso_morphism I) _o) x))%object%morphism) in *.
      clearbody z.
      cut (x = z).
      intros H.
      destruct H.
      match goal with
        [|- _ = (?A ∘ _ ∘ ?B)%morphism] =>
        cutrewrite (A = id);
          [cutrewrite (B = id)|]; try (apply JMeq_eq; destruct e; trivial)
      end.
      {
        auto.
      }      
      {
        cbn_rewrite <- (f_equal (fun u => (u _o x)%object) (left_inverse I)).
        cbn_rewrite <- (f_equal (fun u => (u _o z)%object) (left_inverse I)).
        apply f_equal; trivial.
      }
    Qed.
      
  End LoKan_Cone_Moprh_to_Conv_back_and_forth.

  Section LoKan_Cone_Moprh_from_Conv_forth_and_back.
    Context (Cn : LoKan_Cone p F).
    
    Program Definition LoKan_Cone_Moprh_from_Conv_forth_and_back :
      LoKan_Cone_Morph (LoKan_Cone_Conv_back (LoKan_Cone_Conv Cn)) Cn
      :=
        {|
          cone_morph := NatTrans_id Cn
        |}
    .

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality x.
      cbn.
      Functor_Simplify.
      simpl_ids.
      match goal with
        [|- ((match ?e with _ => _ end)
              ∘ _ ∘ (match ?e with _ => _ end))%morphism = _] =>
        destruct e
      end.
      auto.
    Qed.
      
  End LoKan_Cone_Moprh_from_Conv_forth_and_back.
  
  Section LoKan_Cone_Morph_Conv.
    Context {Cn Cn' : LoKan_Cone p F} (h : LoKan_Cone_Morph Cn Cn').
    
    Program Definition LoKan_Cone_Morph_Conv :
      LoKan_Cone_Morph (LoKan_Cone_Conv Cn) (LoKan_Cone_Conv Cn')
      :=
        {|
          cone_morph := h
        |}
    .

    Next Obligation.
      apply NatTrans_eq_simplify.
      FunExt; cbn.
      Functor_Simplify.
      simpl_ids.
      cbn_rewrite (f_equal (fun x => Trans x) (cone_morph_com h)).
      auto.
    Qed.      

  End LoKan_Cone_Morph_Conv.

  Section LoKan_Cone_Morph_Conv_back.
    Context {Cn Cn' : LoKan_Cone (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I))}
            (h : LoKan_Cone_Morph Cn Cn')
    .
    
    Program Definition LoKan_Cone_Morph_Conv_back :
      LoKan_Cone_Morph (LoKan_Cone_Conv_back Cn) (LoKan_Cone_Conv_back Cn')
      :=
        {|
          cone_morph := h
        |}
    .

    Next Obligation.
      apply NatTrans_eq_simplify.
      FunExt; cbn.
      cbn_rewrite (f_equal (fun x => Trans x) (cone_morph_com h)).
      Functor_Simplify.
      simpl_ids.
      match goal with
        [|-
         ((match ?e with _ => _ end)
            ∘ _ ∘ (match ?e with _ => _ end))%morphism =
         (((match ?e with _ => _ end)
             ∘ _ ∘ (match ?e with _ => _ end)) ∘ _)%morphism
        ] =>
        generalize e
      end.
      intros e.
      repeat rewrite assoc.
      match goal with
        [|-
         (?A1 ∘ ?B1 ∘ ?C1 ∘ ?D1)%morphism =
         (?A2 ∘ ?B2 ∘ ?C2 ∘ ?D2)%morphism
        ] =>
        cutrewrite ((C1 ∘ D1)%morphism = (C2 ∘ D2)%morphism); trivial
      end.
      destruct e; auto.
    Qed.

  End LoKan_Cone_Morph_Conv_back.

  Context (L : Local_Right_KanExt p F).

  Program Definition KanExt_From_Isomorphic_Cat :
    Local_Right_KanExt (p ∘ (iso_morphism I)) (F ∘ (iso_morphism I)) :=
    {|
      LRKE := (LoKan_Cone_Conv L);
      LRKE_morph_ex :=
        fun Cn =>
          LoKan_Cone_Morph_compose
            _
            _
            (LoKan_Cone_Moprh_to_Conv_back_and_forth Cn)
            (LoKan_Cone_Morph_Conv (LRKE_morph_ex L (LoKan_Cone_Conv_back Cn)))
    |}
  .                   

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x.
    set (H :=
           f_equal
             (fun w => Trans w x)
             (LRKE_morph_unique
                L
                (LoKan_Cone_Conv_back Cn)
                (
                  LoKan_Cone_Morph_compose
                    _
                    _
                    (LoKan_Cone_Morph_Conv_back h)
                    (LoKan_Cone_Moprh_from_Conv_forth_and_back _)
                )
                (
                  LoKan_Cone_Morph_compose
                    _
                    _
                    (LoKan_Cone_Morph_Conv_back h')
                    (LoKan_Cone_Moprh_from_Conv_forth_and_back _)
                )
             )
        ).
    cbn in H.
    auto.
  Qed.

End KanExt_From_Isomorphic_Cat.
