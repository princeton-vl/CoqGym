From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Functor Functor.Functor_Ops
        Functor.Representable.Hom_Func.
From Categories Require Import Functor.Functor_Extender.
From Categories Require Import NatTrans.NatTrans NatTrans.Operations
        NatTrans.Func_Cat NatTrans.NatIso.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations
        Ext_Cons.Prod_Cat.Nat_Facts.
From Categories Require Import Adjunction.Adjunction.
From Categories Require Import KanExt.Local  KanExt.LocalFacts.Uniqueness.
From Categories Require Import Basic_Cons.Terminal.

Local Open Scope functor_scope.

(** This module contains conversion from local kan extension defiend as cones
to local kan extensions defined through hom functor. *)

Section Local_Right_KanExt_to_Hom_Local_Right_KanExt.
  Context {C C' : Category} {p : C –≻ C'}
          {D : Category} {F : C –≻ D}
          (lrke : Local_Right_KanExt p F).

  (** The left to right side of Hom_Local_Right_KanExt isomorphism. *)
  Program Definition Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_LR :
    (((@Fix_Bi_Func_2 _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D)))
        ∘ (Left_Functor_Extender p D)^op)
       –≻ (@Fix_Bi_Func_2 _ (Func_Cat C' D)
                          _ lrke (Hom_Func (Func_Cat C' D))))%nattrans :=
    {|
      Trans :=  fun c h => LRKE_morph_ex lrke {|cone_apex := c; cone_edge := h|}
    |}.

  Next Obligation.
  Proof.
    extensionality x.
    repeat rewrite NatTrans_id_unit_left.
    match goal with
      [|- cone_morph (LRKE_morph_ex lrke ?A) = ?X] =>
      match X with
        ((cone_morph ?C) ∘ ?B)%nattrans =>
        change X with
        (cone_morph
           (LoKan_Cone_Morph_compose
              _
              _
              (Build_LoKan_Cone_Morph
                 p F A {|cone_apex := c; cone_edge := x|} h eq_refl) C
           )
        )
      end
    end.
    apply LRKE_morph_unique.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_LR_obligation_1.
  Qed.

  (** The right to left side of Hom_Local_Right_KanExt isomorphism. *)
  Program Definition Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_RL :
    ((@Fix_Bi_Func_2 _ (Func_Cat C' D) _ lrke (Hom_Func (Func_Cat C' D)))
       –≻ ((@Fix_Bi_Func_2 _ (Func_Cat C D) _ F (Hom_Func (Func_Cat C D)))
             ∘ (Left_Functor_Extender p D)^op
             ))%nattrans
    :=
    {|
      Trans :=  fun c h => (lrke ∘ (h ∘_h (NatTrans_id p)))%nattrans
    |}.
 
  Next Obligation.
  Proof.
    extensionality x.
    repeat rewrite NatTrans_id_unit_left.
    rewrite NatTrans_compose_assoc.
    rewrite NatTrans_comp_hor_comp.
    rewrite NatTrans_id_unit_right.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_RL_obligation_1.
  Qed.

  (** Conversion from Local_Right_KanExt Hom_Local_Right_KanExt isomorphism. *)
  Program Definition Local_Right_KanExt_to_Hom_Local_Right_KanExt :
    Hom_Local_Right_KanExt p F :=
    {|
      HLRKE := (cone_apex (LRKE lrke));
      HLRKE_Iso :=
        {|
          iso_morphism := Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_LR;
          inverse_morphism :=
            Local_Right_KanExt_to_Hom_Local_Right_KanExt_Iso_RL
        |}
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality h; extensionality x.
    symmetry.
    apply (cone_morph_com
             (LRKE_morph_ex lrke {| cone_apex := h; cone_edge := x |})).
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality h; extensionality x.
    cbn in *.
    match goal with
      [|- cone_morph (LRKE_morph_ex lrke ?A) = ?X] =>
      change X with (cone_morph (Build_LoKan_Cone_Morph p F A lrke x eq_refl));
        apply (LRKE_morph_unique lrke A)
    end.
  Qed.

End Local_Right_KanExt_to_Hom_Local_Right_KanExt.
