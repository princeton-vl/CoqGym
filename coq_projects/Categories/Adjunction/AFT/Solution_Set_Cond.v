From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.

(** The solution set condition. In Freyd's adjoint functor theorem
it is assumed that (Comma (Func_From_SingletonCat x) G) satisfies
solution set condition. 

A category C satisfies solution set condition if there is a type A,
a function f : A → C such that for any object (c : C) there exists
a (t : A) such that there is a morphism h : (f t) –≻ c. In short,
f is jointly weakly initial.
*)
Record Solution_Set_Cond (C : Category) :=
  {
    SSC_Type : Type;
    SSC_Objs : SSC_Type → C;
    SSC_jointly_weakly_initial :>
      ∀ (c : C), {t : SSC_Type & ((SSC_Objs t) –≻ c)%morphism}
  }
.

Arguments SSC_Type {_} _.
Arguments SSC_Objs {_} _ _.
Arguments SSC_jointly_weakly_initial {_} _ _.

From Categories Require Import Limits.Limit Limits.GenProd_GenSum.
From Categories Require Import Functor.Functor.
From Categories Require Import NatTrans.NatTrans.
From Categories Require Import
        Basic_Cons.Terminal
        Basic_Cons.Equalizer
        Basic_Cons.Limits
        Basic_Cons.Facts.Equalizer_Monic
.
From Categories Require Import Archetypal.Discr.Discr.


(** We show that a category that is complete and satisfies solution 
    set condition has an initial object. This initial object is the
    equalizer of all endo-morphisms d : W –≻ W,
    where W is the generalized product of the function (SSC_Objs) of
    the solution set condition. *)
Section Complete_SSC_Initial.
  Context
    {C : Category}
    (CC : Complete C)
    (SSC : Solution_Set_Cond C)
  .

  (** The product of objects producing SSC. *)
  Definition SSC_Prod : (Π (SSC_Objs SSC))%object
    :=
      (LimitOf (Discr_Func (SSC_Objs SSC))).

  (** SSC_Prod is weakly initial. I.e., it has an arrow (not necessarily unique)
to any other object. *)
  Definition SSC_Prod_WI (c : C) :
    (SSC_Prod –≻ c)%morphism
    :=
      (
        (projT2 (SSC_jointly_weakly_initial SSC c))
          ∘
          (
            Trans
              (cone_edge SSC_Prod)
              (projT1 (SSC_jointly_weakly_initial SSC c))
          )
      )%morphism
  .

  (** The constant function from endomorphisms of SSC_Prod that
returns SSC_Prod.  *)
  Definition endomorph_const (h : (SSC_Prod –≻ SSC_Prod)%morphism) : C
    :=
      SSC_Prod
  .

  (** The product of SSC_Prod with endomorphisms as index. *)
  Definition Endo_Prod : (Π endomorph_const)%object
    :=
      (LimitOf (Discr_Func endomorph_const)).


  (** Cone to (Discr_Func endomorph_const) that maps to ids. *)
  Program Definition Cone_Endo_Prod_ids : Cone (Discr_Func endomorph_const)
    :=
      {|
        cone_apex :=
          {|
            FO := fun _ => SSC_Prod;
            FA := fun _ _ _ => id
          |};
        cone_edge :=
          {|
            Trans := fun _ => id
          |}
      |}
  .

  (** Morphism that projects to ids. *)
  Definition morph_to_Endo_Prod_ids : (SSC_Prod –≻ Endo_Prod)%morphism
    :=
      Trans (LRKE_morph_ex Endo_Prod Cone_Endo_Prod_ids) tt.

  (** Cone to (Discr_Func endomorph_const) that maps to ids. *)
  Program Definition Cone_Endo_Prod_endomorphs :
    Cone (Discr_Func endomorph_const)
    :=
      {|
        cone_apex :=
          {|
            FO := fun _ => SSC_Prod;
            FA := fun _ _ _ => id
          |};
        cone_edge :=
          {|
            Trans := fun h => h
          |}
      |}
  .

  (** Morphism that projects to endomorphisms. *)
  Definition morph_to_Endo_Prod_endomorphs : (SSC_Prod –≻ Endo_Prod)%morphism
    :=
      Trans (LRKE_morph_ex Endo_Prod Cone_Endo_Prod_endomorphs) tt.

  Definition ids_endomorphs_equalizer :
    Equalizer
      morph_to_Endo_Prod_endomorphs
      morph_to_Endo_Prod_ids
    :=
      Equalizer_as_Limit
        morph_to_Endo_Prod_endomorphs
        morph_to_Endo_Prod_ids
        (LimitOf
           (Equalizer_Producing_Func
              morph_to_Endo_Prod_endomorphs
              morph_to_Endo_Prod_ids)
        )
  .

  (** ids_endomorphs_equalizer is weakly initial. I.e., it has an arrow 
(not necessarily unique) to any other object. *)
  Definition ids_endomorphs_equalizer_WI (c : C) :
    (ids_endomorphs_equalizer –≻ c)%morphism
    :=
      (SSC_Prod_WI c ∘ equalizer_morph ids_endomorphs_equalizer)%morphism
  .

  (** composing any endomorphism after equalizer morphism of 
      ids_endomorphs_equalizer is the same as the equalizer
      morphism of ids_endomorphs_equalizer.
*)
  Theorem ids_endomorphs_equalizer_morph_neutralizes_endomorphs
          (d : (SSC_Prod –≻ SSC_Prod)%morphism)
    :
      (d ∘ equalizer_morph ids_endomorphs_equalizer)%morphism
      = equalizer_morph ids_endomorphs_equalizer
  .
  Proof.
    assert (H :=
              f_equal
                (fun w => ((Trans Endo_Prod d) ∘ w)%morphism)
                (equalizer_morph_com ids_endomorphs_equalizer)
           ).
    cbn -[equalizer_morph ids_endomorphs_equalizer Endo_Prod] in H.
    unfold morph_to_Endo_Prod_endomorphs, morph_to_Endo_Prod_ids in H.
    repeat rewrite assoc_sym in H.
    assert (V :=
           f_equal
             (fun w :
                    ((Functor_Ops.Functor_compose
                        (Functor_To_1_Cat
                           (Discr_Cat (SSC_Prod –≻ SSC_Prod)%morphism))
                        Cone_Endo_Prod_endomorphs)
                       –≻ Discr_Func endomorph_const)%nattrans
              => Trans w d)
             (cone_morph_com
                (LRKE_morph_ex Endo_Prod Cone_Endo_Prod_endomorphs))
        ).
    cbn -[LRKE_morph_ex Endo_Prod] in V.
    rewrite From_Term_Cat in V.
    simpl_ids in V.
    rewrite <- V in H.
    clear V.
    assert (V :=
           f_equal
             (fun w :
                    ((Functor_Ops.Functor_compose
                       (Functor_To_1_Cat
                          (Discr_Cat (SSC_Prod –≻ SSC_Prod)%morphism))
                       Cone_Endo_Prod_ids)
                       –≻ Discr_Func endomorph_const)%nattrans
              => Trans w d)
             (cone_morph_com (LRKE_morph_ex Endo_Prod Cone_Endo_Prod_ids))
        ).
    cbn -[LRKE_morph_ex Endo_Prod] in V.
    rewrite From_Term_Cat in V.
    simpl_ids in V.
    rewrite <- V in H.
    clear V.
    auto.
  Qed.

  Section equalizer_of_morphs_from_ids_endomorphs_equalizer_iso.
    Context
      {d : C}
      (f g : (ids_endomorphs_equalizer –≻ d)%morphism)
    .

    (** Let's show ids_endomorphs_equalizer with V, we construct for any pair of
         morphisms f, g : V –≻ d, their equalizer (U, e : U –≻ V).
     *)
    Definition equalizer_of_morphs_from_ids_endomorphs_equalizer
      :
        Equalizer f g
      :=
        Equalizer_as_Limit
          f
          g
          (LimitOf (Equalizer_Producing_Func f g))
    .

    Theorem equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_RI :
      ((equalizer_morph (equalizer_of_morphs_from_ids_endomorphs_equalizer))
         ∘
         ((SSC_Prod_WI _)
            ∘ (equalizer_morph ids_endomorphs_equalizer)))%morphism
      =
      id.
    Proof.
      apply (
          mono_morphism_monomorphic
            (@Equalizer_Monic _ _ _ _ _ ids_endomorphs_equalizer)
        ).
      rewrite id_unit_right.
      repeat rewrite assoc_sym.
      apply ids_endomorphs_equalizer_morph_neutralizes_endomorphs.      
    Qed.

    Theorem equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_LI :
      (((SSC_Prod_WI _) ∘ (equalizer_morph ids_endomorphs_equalizer))
         ∘
         (equalizer_morph (equalizer_of_morphs_from_ids_endomorphs_equalizer))
      )%morphism
      =
      id.
    Proof.
      apply (
          mono_morphism_monomorphic
            (@Equalizer_Monic _ _ _ _ _
                              equalizer_of_morphs_from_ids_endomorphs_equalizer)
        ).
      unfold Equalizer_Monic.
      cbn [mono_morphism].
      rewrite assoc_sym.
      simpl_ids.
      trivial.
      apply equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_RI.
    Qed.
    
    (** Let's show ids_endomorphs_equalizer with V, then, for any pair of
        morphisms f, g : V –≻ d, we have their equalizer (U, e : U –≻ V)
        forms an isomorphism (U ≃ V).
     *)
    Program Definition equalizer_of_morphs_from_ids_endomorphs_equalizer_iso
      :
        ((equalizer_of_morphs_from_ids_endomorphs_equalizer)
           ≃ ids_endomorphs_equalizer)%isomorphism
      :=
        {|
          iso_morphism := equalizer_morph
                            (equalizer_of_morphs_from_ids_endomorphs_equalizer);
          inverse_morphism :=
            ((SSC_Prod_WI _)
               ∘ (equalizer_morph ids_endomorphs_equalizer))%morphism;
          left_inverse :=
            equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_LI;
          right_inverse :=
            equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_RI
        |}
    .

  End equalizer_of_morphs_from_ids_endomorphs_equalizer_iso.

  Local Obligation Tactic := idtac.
  
  Program Definition Complete_SSC_Initial : (𝟘_ C)%object
    :=
      {|
        terminal := ids_endomorphs_equalizer;
        t_morph := ids_endomorphs_equalizer_WI
      |}
  .

  Next Obligation.
  Proof.
    intros d f g.
    cbn -[ids_endomorphs_equalizer] in *.
    assert (H :=
              f_equal
                (fun w => (f ∘ w)%morphism)
                (equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_RI f g)).
    cbn -[ids_endomorphs_equalizer
            equalizer_of_morphs_from_ids_endomorphs_equalizer] in H.
    simpl_ids in H.
    rewrite <- H.
    clear H.
    assert (H :=
              f_equal
                (fun w => (g ∘ w)%morphism)
                (equalizer_of_morphs_from_ids_endomorphs_equalizer_iso_RI f g)).
    cbn -[ids_endomorphs_equalizer
            equalizer_of_morphs_from_ids_endomorphs_equalizer] in H.
    simpl_ids in H.
    etransitivity; [|apply H].
    clear H.
    repeat rewrite assoc_sym.
    match goal with
      [|- (((f ∘ ?A) ∘ ?B) ∘ ?C = _)%morphism] =>
      apply (f_equal (fun w => ((w ∘ B) ∘ C)%morphism))
    end.
    apply (equalizer_morph_com
             (equalizer_of_morphs_from_ids_endomorphs_equalizer f g)).
  Qed.

End Complete_SSC_Initial.
