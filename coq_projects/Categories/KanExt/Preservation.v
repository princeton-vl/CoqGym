From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func.
From Categories Require Import Functor.Functor_Extender.
From Categories Require Import NatTrans.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Main.
From Categories Require Import Adjunction.Adjunction Adjunction.Duality Adjunction.Adj_Facts.
From Categories Require Import KanExt.Local KanExt.LocalFacts.Main.

Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).

Local Open Scope functor_scope.

(** Local right kan extensions are preserved by right adjoints and local left
    kan extensions are preserved by left adjoints. *)
Section Right_Adjoint_Preserves_Hom_Local_Right_KanExt.
  Context
    {C C' : Category}
    (p : C –≻ C')
    {D : Category}
    (F : C –≻ D)
    (hlrke : Hom_Local_Right_KanExt p F)
    {E : Category}
    {L : E –≻ D}
    {R : D –≻ E}
    (adj : UCU_Adjunct L R)
  .
  
  (** Hom_Func_{Func_Cat C E}(- ∘ p, R ∘ F)
        ≃ Hom_Func_{Func_Cat C D}(L ∘ - ∘ p, F) *)
  Local Definition Ext_p_F_Hom_Adjunct_Lifted :=
    ((
        ((Fix_Bi_Func_2_NatIso (Hom_Adjunct_Lifted adj C) F)
           ∘ (Fix_Bi_Func_2_Functor_id_swap_NatIso _ _ F)⁻¹
        )
          ∘_h
          (NatTrans_id_Iso (Left_Functor_Extender p E)^op)
       )⁻¹
    )%isomorphism%natiso.
  
  
  Local Definition Conv_1 :=
    (
      NatIso_Functor_assoc
       ((Left_Functor_Extender p E)^op)
       ((Right_Functor_Extender L C)^op)
       (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D)))
    ).

  Local Definition Conv_2 :=
    (
      (
        (NatTrans_id_Iso (@Fix_Bi_Func_2
                            _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D))))
          ∘_h ((Right_Left_Functor_Extension_Iso p L)⁻¹)^op
      )⁻¹
    )%isomorphism%natiso.

  Local Definition Conv_3 :=
    (
      (
        NatIso_Functor_assoc
          ((Right_Functor_Extender L C')^op)
          ((Left_Functor_Extender p D)^op)
          (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func (Func_Cat C D)))
      )⁻¹
    )%isomorphism.

  Local Definition Conv := ((Conv_3 ∘ Conv_2) ∘ Conv_1)%isomorphism.

  Local Definition Ext_L_HLRKE_Iso :=
    (
      (HLRKE_Iso hlrke)
        ∘_h (NatTrans_id_Iso (Right_Functor_Extender L C')^op)
    )%natiso.

  Local Definition Fix2_hlrke_Hom_Adjunct_Lifted :=
    (
      (Fix_Bi_Func_2_NatIso (Hom_Adjunct_Lifted adj C') (hlrke))
        ∘ (Fix_Bi_Func_2_Functor_id_swap_NatIso _ _ (hlrke))⁻¹
    )%isomorphism.

  Local Definition Local_Preservation_Iso_underlying :=
    (
      (
        (Fix2_hlrke_Hom_Adjunct_Lifted ∘ Ext_L_HLRKE_Iso)
          ∘Conv
      )
        ∘ Ext_p_F_Hom_Adjunct_Lifted
    )%isomorphism
  .

  Local Definition Left_simplifier :=
    (
      (
        (
          (Fix_Bi_Func_2_NatIso
             (Func_Prod_of_ids_NatIso (Hom_Func (Func_Cat C E))) (R ∘ F))
            ∘ (Fix_Bi_2_Func_Prod_Func_NatIso
                 (Functor_id (Func_Cat C E) ^op)
                 (Right_Functor_Extender R C)
                 (Hom_Func (Func_Cat C E))
                 F
              )
        )⁻¹
      )
        ∘_h (NatTrans_id_Iso (Left_Functor_Extender p E)^op)
    )%isomorphism%natiso
  .

  Local Definition Right_simplifier :=
    (
      (
        Fix_Bi_Func_2_NatIso
          (Func_Prod_of_ids_NatIso (Hom_Func (Func_Cat C' E)))
          (R ∘ hlrke)
      )
        ∘
        (
          Fix_Bi_2_Func_Prod_Func_NatIso
            (Functor_id (Func_Cat C' E) ^op)
            (Right_Functor_Extender R C')
            (Hom_Func (Func_Cat C' E))
            (hlrke)
        )
      )%isomorphism
  .
  
  Definition Local_Preservation_Iso :=
    (Right_simplifier ∘ (Local_Preservation_Iso_underlying
                           ∘ Left_simplifier))%isomorphism
  .

  Definition Right_Adjoint_Preserves_Hom_Local_Right_KanExt :
    Hom_Local_Right_KanExt p (R ∘ F) :=
    {|
      HLRKE := (R ∘ (HLRKE hlrke));
      HLRKE_Iso := Local_Preservation_Iso
    |}.
  
End Right_Adjoint_Preserves_Hom_Local_Right_KanExt.

Section Right_Adjoint_Preserves_Local_Right_KanExt.
  Context {C C' : Category}
          (p : C –≻ C')
          {D : Category}
          (F : C –≻ D)
          (lrke : Local_Right_KanExt p F)
          {E : Category}
          {L : E –≻ D}
          {R : D –≻ E}
          (adj : UCU_Adjunct L R)
  .
  
  Definition Right_Adjoint_Preserves_Local_Right_KanExt :
    Local_Right_KanExt p (R ∘ F) :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt
      (
        Right_Adjoint_Preserves_Hom_Local_Right_KanExt
          _
          _
          (Local_Right_KanExt_to_Hom_Local_Right_KanExt lrke)
          adj
      )
  .
  
End Right_Adjoint_Preserves_Local_Right_KanExt.

Section Left_Adjoint_Preserves_Hom_Local_Left_KanExt.
  Context {C C' : Category}
          (p : C –≻ C')
          {D : Category}
          (F : C –≻ D)
          (hllke : Hom_Local_Left_KanExt p F)
          {E : Category}
          {L : D –≻ E}
          {R : E –≻ D}
          (adj : UCU_Adjunct L R)
  .
  
  Definition Left_Adjoint_Preserves_Hom_Local_Left_KanExt :
    Hom_Local_Left_KanExt p (L ∘ F) :=
    Right_Adjoint_Preserves_Hom_Local_Right_KanExt
      _
      _
      hllke
      (Adj_to_UCU_Adj _ _ (Adjunct_Duality (UCU_Adj_to_Adj _ _ adj)))
  .
  
End Left_Adjoint_Preserves_Hom_Local_Left_KanExt.

Section Left_Adjoint_Preserves_Local_Left_KanExt.
  Context {C C' : Category}
          (p : C –≻ C')
          {D : Category}
          (F : C –≻ D)
          (hllke : Local_Left_KanExt p F)
          {E : Category}
          {L : D –≻ E}
          {R : E –≻ D}
          (adj : UCU_Adjunct L R)
  .
  
  Definition Left_Adjoint_Preserves_Local_Left_KanExt :
    Local_Left_KanExt p (L ∘ F) :=
    Right_Adjoint_Preserves_Local_Right_KanExt
      _
      _
      hllke
      (Adj_to_UCU_Adj _ _ (Adjunct_Duality (UCU_Adj_to_Adj _ _ adj)))
  .
  
End Left_Adjoint_Preserves_Local_Left_KanExt.
