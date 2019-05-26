From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.Morphisms.
From Categories Require Import NatTrans.NatTrans
        NatTrans.Operations
        NatTrans.Func_Cat
        NatTrans.Morphisms
        NatTrans.NatIso.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import PreSheaf.PreSheaf PreSheaf.Terminal.
From Categories Require Import Archetypal.Discr.Discr.


(** In this section we show that all components of a monic
morphism of presheaves are monic. 

We do this by showing that given a monic morphism of presheaves
N : F ≫–> G we can convert any function from f : A → (F c) to
a morphism of presheaves (PSh(f) : Psh(A) –≻ F) such that this
morphism at c gives exactly f.
*)
Section PreSheaf_Monic_components_Monic.
  Context
    {C : Category}
    {F : PreSheaf C}
  .

  Section PMCM_PreSheaf_representing_d.
    Context (c : C) (d : Type).

    Local Hint Extern 1 => progress cbn.

    Program Definition PMCM_PreSheaf_representing_d : PreSheaf C
      :=
        {|
          FO := fun c' => ((Hom C c' c) * d)%type;
          FA := fun o o' u x => (compose C u (fst x), snd x)
        |}
    .

  End PMCM_PreSheaf_representing_d.


  Context
    {G : PreSheaf C}
    (N : @Monic (PShCat C) F G)
    (c : C)
  .
    
  Section PreSheaf_Monic_components_Monic_is_Monic.
    Context
      (d : Type)
      (g h : d → (F _o)%object c)
      (H : (fun x => Trans (mono_morphism N) c (g x))
           = (fun x => Trans (mono_morphism N) c (h x)))
    .

(*    Local Hint Extern 1 => progress cbn.*)

    Local Hint Extern 1 =>
    match goal with
      [|- context [(F _a)%morphism (?A ∘ ?B)%morphism] ] =>
      cbn_rewrite (F_compose F A B)
    end.
    
    Program Definition PMCM_PreSheaf_morph_of_function
            (f : d → (F _o)%object c)
      : (PMCM_PreSheaf_representing_d c d –≻ F)%nattrans
      :=
        {|
          Trans := fun o x => (F _a (fst x))%morphism (f (snd x))
        |}
    .

    Theorem PMCM_N_co_equalizes :
      ((mono_morphism N) ∘ (PMCM_PreSheaf_morph_of_function g))%nattrans
      = ((mono_morphism N) ∘ (PMCM_PreSheaf_morph_of_function h))%nattrans.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality x.
      extensionality y.
      destruct y as [y1 y2].
      cbn in *.
      set (W := equal_f (Trans_com (mono_morphism N) y1)).
      cbn in W.
      do 2 rewrite W.
      rewrite (equal_f H).
      trivial.
    Qed.    

    Theorem PreSheaf_Monic_components_is_Monic : g = h.
    Proof.
      extensionality m.
      assert (W :=
                f_equal
                  (fun w : (PMCM_PreSheaf_representing_d c d –≻ F)%nattrans =>
                     Trans w c (id, m))
                  (mono_morphism_monomorphic N _ _ _ PMCM_N_co_equalizes)
             ).
      cbn in W.
      rewrite (F_id F) in W.
      trivial.
    Qed.

  End PreSheaf_Monic_components_Monic_is_Monic.

  Definition PreSheaf_Monic_components_Monic_Monic :
    Monic (F _o c)%object (G _o c)%object
    :=
      {|
        mono_morphism := Trans (mono_morphism N) c;
        mono_morphism_monomorphic :=
          PreSheaf_Monic_components_is_Monic
      |}.
  
End PreSheaf_Monic_components_Monic.

(** In this section we show that all components of an epic
morphism of presheaves are epic.

We do this by showing that given an epic morphism of presheaves
N : F –≫ G we can convert any function from f : (G c) → A to
a morphism of presheaves (PSh(f) : G –≻ Psh(A)) such that this
morphism at c gives exactly f.
*)
Section PreSheaf_Epic_components_Epic.
  Context
    {C : Category}
    {F G : PreSheaf C}
    (N : @Epic (PShCat C) F G)
    (c : C)
  .
  
  Section PreSheaf_Epic_components_is_Epic.
    Context
      (d : Type)
      (g h : (G _o)%object c → d)
      (H : (fun x => g (Trans (mono_morphism N) c x)) =
           (fun x => h (Trans (mono_morphism N) c x)))
    .

    Local Hint Extern 1 => progress cbn.

    Local Hint Extern 1 => rewrite assoc.

    Program Definition PECE_PreSheaf_representing_d : PreSheaf C
      :=
        {|
          FO := fun c' => (((Hom C c c') → d))%object%morphism%type;
          FA := fun o o' u x y => (x (compose C y u))
        |}
    .

    Local Hint Extern 1 =>
    match goal with
      [|- context [(G _a)%morphism (?A ∘ ?B)%morphism] ] =>
      cbn_rewrite (F_compose G A B)
    end.
    
    Program Definition PECE_PreSheaf_morph_of_function
            (f : (G _o)%object c → d)
      : (G –≻ PECE_PreSheaf_representing_d)%nattrans
      :=
        {|
          Trans := fun o x y => f ((G _a y)%morphism x)
        |}
    .
    
    Theorem PECE_N_co_equalizes :
      ((PECE_PreSheaf_morph_of_function g) ∘ (mono_morphism N))%nattrans =
      ((PECE_PreSheaf_morph_of_function h) ∘ (mono_morphism N))%nattrans.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality x.
      extensionality y.
      extensionality z.
      cbn in *.
      set (W := equal_f (Trans_com (mono_morphism N) z)).
      cbn in W.
      rewrite <- W.
      rewrite (equal_f H).
      trivial.
    Qed.    

    Theorem PreSheaf_Epic_components_is_Epic : g = h.
    Proof.
      extensionality m.
      assert (W :=
                f_equal
                  (fun w : (G –≻ PECE_PreSheaf_representing_d)%nattrans =>
                     Trans w c m id)
                  (mono_morphism_monomorphic N _ _ _ PECE_N_co_equalizes)
             ).
      cbn in W.
      rewrite (F_id G) in W.
      trivial.
    Qed.

End PreSheaf_Epic_components_is_Epic.

  Program Definition PreSheaf_Epic_components_Epic :
    Epic (F _o c)%object (G _o c)%object
    :=
      {|
        mono_morphism := Trans (mono_morphism N) c;
        mono_morphism_monomorphic :=
          PreSheaf_Epic_components_is_Epic
      |}.
  
End PreSheaf_Epic_components_Epic.

Local Hint Extern 1 => match goal with
                        [|- context [(?F _a id)%morphism]] => rewrite (F_id F)
                      end.
Local Hint Extern 1 =>
match goal with
  [|- context [(?F _a (?f ∘ ?g))%morphism]] =>
  cbn_rewrite (F_compose F f g)
end.

Local Hint Extern 1 =>
match goal with
  [|- context [Trans ?f _ ((?F _a)%morphism ?h _)]] =>
  cbn_rewrite (equal_f (Trans_com f h))
end.

Local Hint Extern 1 => progress cbn in *.

(** In this section we show that a monic presheaf morphism can be split
into to presheaf morphisms one iso and one monic.

This result is inherited from that in Type_Cat and is proven similarly.
*)
Section Monic_PreSheaf_Iso_Monic_Factorization.
  Context
    {C : Category}
    {F G : PreSheaf C}
    (N : @Monic (PShCat C) F G)
  .

  Lemma sigT_sig_proof_irrelevance
        {T : Type}
        {P : T → Type}
        {Q : ∀ x, (P x) → Prop}
        (A B : sigT (fun y => sig (Q y)))
        (H : projT1 A = projT1 B)
        (H' :
           (
             proj1_sig
               (
                 match H in _ = u return
                       {x : P u | Q u x}
                 with
                   eq_refl => projT2 A
                 end
               )
           )
           =
           (proj1_sig (projT2 B)))
    :
      A = B
  .
  Proof.
    destruct A as [Ax [Ay HA]].
    destruct B as [Bx [By HB]].
    cbn in *.
    transitivity
      (
        existT
          (fun y : T => {x : P y | Q y x})
          Bx
          match H in _ = u return
                {x : P u | Q u x}
          with
            eq_refl => (exist (Q Ax) Ay HA)
          end
      ).
    {
      destruct H; trivial.
    }    
    {
      match goal with
        [|- existT _ ?A ?B = existT _ ?A ?B'] =>
        cutrewrite (B = B');trivial
      end.
      apply sig_proof_irrelevance; trivial.
    }
  Qed.

  Local Hint Extern 1 =>
  match goal with
    [x : {_ : _ & {_ : _ | _}} |- _] =>
    let H :=
        fresh "H"
    in
    let x1 :=
        fresh x "1"
    in
    let x2 :=
        fresh x "2"
    in
    destruct x as [x1 [x2 H]]
  end.

  Local Hint Extern 1 =>
  match goal with
    [x : Monic_Image_of |- _] =>
    let H :=
        fresh "H"
    in
    let x1 :=
        fresh x "1"
    in
    let x2 :=
        fresh x "2"
    in
    destruct x as [x1 [x2 H]]
  end.

  Local Hint Extern 1 =>
  match goal with
    [|- ?A = ?B] =>
    assert (H : (projT1 A) = (projT1 B));
      [|
       apply (sigT_sig_proof_irrelevance _ _ H);
         destruct H
      ]
  end.
  
  Program Definition Monic_PreSheaf_Image_of : PreSheaf C
    :=
      {|
        FO := fun x => @Monic_Image_of _ _ (Trans (mono_morphism N) x);
        FA := fun c c' h x =>
                existT _ (G _a h (projT1 x))%morphism
                       (exist _ (F _a h (proj1_sig (projT2 x)))%morphism _)
      |}
  .
  
  Program Definition Monic_PreSheaf_Morph_From_Monic_PreSheaf_Image_of_forward :
    (Monic_PreSheaf_Image_of –≻ G)%nattrans
    :=
      {|
        Trans := fun x => @Monic_From_Image_forward _ _ (Trans (mono_morphism N) x)
      |}.
  
  Program Definition Monic_PreSheaf_From_Monic_PreSheaf_Image_of_back :
    (Monic_PreSheaf_Image_of –≻ F)%nattrans
    :=
      {|
        Trans := fun x => @Monic_From_Image_back _ _ (Trans (mono_morphism N) x)
      |}.

  Program Definition Monic_PreSheaf_To_Monic_PreSheaf_Image_of :
    (F –≻ Monic_PreSheaf_Image_of)%nattrans
    :=
      {|
        Trans := fun x => @Monic_To_Image _ _ (Trans (mono_morphism N) x)
      |}.

  Definition Monic_PreSheaf_Iso_Monic_Factor_Monic :
    @Monic (PShCat C) Monic_PreSheaf_Image_of G.
  Proof.
    eapply (@is_Monic_Monic
              (PShCat C)
              _
              _
              Monic_PreSheaf_Morph_From_Monic_PreSheaf_Image_of_forward
           )
    .
    apply is_Monic_components_is_Monic.
    intros c.
    set (W := fun A B f H => mono_morphism_monomorphic
                            (@Monic_Iso_Monic_Factor_Monic A B f H)).
    unfold is_Monic in *.
    cbn in *.
    apply W.
    apply PreSheaf_Monic_components_is_Monic.
  Defined.

  Program Definition Monic_PreSheaf_Iso_Monic_Factor_Monic_Iso :
    @Isomorphism (PShCat C) F Monic_PreSheaf_Image_of
    :=
      {|
        iso_morphism := Monic_PreSheaf_To_Monic_PreSheaf_Image_of;
        inverse_morphism := Monic_PreSheaf_From_Monic_PreSheaf_Image_of_back
      |}
  .

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x.
    extensionality y.
    cbn in *.
    apply (equal_f Monic_To_Image_form_split_epic).
  Qed.

  Theorem split_Epic_Monic_Factorization :
    (mono_morphism N) =
    (
      (mono_morphism Monic_PreSheaf_Iso_Monic_Factor_Monic)
        ∘
        (iso_morphism Monic_PreSheaf_Iso_Monic_Factor_Monic_Iso)
    )%nattrans.
  Proof.
    apply NatTrans_eq_simplify; trivial.
  Qed.
  
End Monic_PreSheaf_Iso_Monic_Factorization.

(** In this section we show that a presheaf morphism can be split
into to presheaf morphisms one epic and one monic.

This result is inherited from that in Type_Cat and is proven similarly.
The only difference is that in Type_Cat the epimorphism is split epic
while in presheaves, the morphisms back are not guaranteed to form a
natural transformation.
*)
Section PreSheaf_Epic_Monic_Factorization.
  Context
    {C : Category}
    {F G : PreSheaf C}
    (N : (F –≻ G)%nattrans)
  .

  Local Hint Extern 1 =>
  match goal with
    [x : {_ : _ | ∃ _, _} |- _] =>
    let H :=
        fresh "H"
    in
    let x1 :=
        fresh x "1"
    in
    let x2 :=
        fresh x "2"
    in
    destruct x as [x1 [x2 H]]
  end.

  Local Hint Extern 1 =>
  match goal with
    [x : Image_of _ |- _] =>
    let H :=
        fresh "H"
    in
    let x1 :=
        fresh x "1"
    in
    let x2 :=
        fresh x "2"
    in
    destruct x as [x1 [x2 H]]
  end.

  Local Obligation Tactic := basic_simpl; auto 10.
  
  Program Definition PreSheaf_Image_of : PreSheaf C
    :=
      {|
        FO := fun x => @Image_of _ _ (Trans N x);
        FA := fun c c' h x => exist _ (G _a h (proj1_sig x))%morphism _
      |}
  .

  Next Obligation.
  Proof.
    destruct x as [x [y []]].
    exists (F _a h y)%morphism; auto.
  Qed.

  Program Definition PreSheaf_From_Image_Forward :
    (PreSheaf_Image_of –≻ G)%nattrans
    :=
      {|
        Trans := fun x => @From_Image_forward _ _ (Trans N x)
      |}.
  
  Definition PreSheaf_Epic_Monic_Factor_Monic :
    @Monic (PShCat C) PreSheaf_Image_of G.
  Proof.
    eapply (@is_Monic_Monic
              (PShCat C)
              _
              _
              PreSheaf_From_Image_Forward
           )
    .
    apply is_Monic_components_is_Monic.
    intros c.
    set (W := fun A B f => mono_morphism_monomorphic
                          (@Epic_Monic_Factor_Monic A B f)).
    unfold is_Monic in *; cbn in *.
    apply W.
  Defined.

  Local Hint Extern 1 => apply sig_proof_irrelevance.
  
  Program Definition PreSheaf_To_Image :
    (F –≻ PreSheaf_Image_of)%nattrans
    :=
      {|
        Trans := fun x => To_Image (Trans N x)
      |}.

  Definition PreSheaf_Epic_Monic_Factor_Epic :
    @Epic (PShCat C) F PreSheaf_Image_of.
  Proof.
    eapply (@is_Monic_Monic
              ((PShCat C) ^op)
              _
              _
              PreSheaf_To_Image
           )
    .
    apply is_Epic_components_is_Epic.
    set (W := fun A B f => mono_morphism_monomorphic
                          (is_split_Monic_Monic
                             (@Epic_Monic_Factor_split_Epic A B f))).
    unfold is_Epic, is_Monic in *; cbn in *.
    intros c.
    apply W.
  Defined.

End PreSheaf_Epic_Monic_Factorization.
