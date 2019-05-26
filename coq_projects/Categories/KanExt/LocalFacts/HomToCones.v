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
From Categories Require Import KanExt.Local.
From Categories Require Import Basic_Cons.Terminal.

Local Open Scope functor_scope.

(** This module contains conversion from local kan extensions defined through
    hom functor to local kan extensions defined through cones. *)
Section Hom_Local_Right_KanExt_to_Local_Right_KanExt.
  Context {C C' : Category} {p : C –≻ C'}
          {D : Category} {F : C –≻ D}
          (hlrke : Hom_Local_Right_KanExt p F).

  (** The cone that is the kan extension. *)
  Definition Hom_Local_Right_KanExt_to_Local_Right_KanExt_Terminal_Cone :
    LoKan_Cone p F :=
    {|
      cone_apex := hlrke;
      cone_edge :=
        Trans (inverse_morphism (HLRKE_Iso hlrke)) hlrke (NatTrans_id hlrke)
    |}.

  (** The cone we just constructed is (as we will prove) the local kan
      extension and thus the terminal cone. So we abbreviate it as TCONE. *)
  Local Notation TCONE :=
    Hom_Local_Right_KanExt_to_Local_Right_KanExt_Terminal_Cone (only parsing).

  (** Given a cone Cn, we construct a cone morph from Cn to the cone that is the
local kan extension. *)
  Section Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone.
    Context (Cn : LoKan_Cone p F).

    Program Definition
            Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone :
      LoKan_Cone_Morph Cn TCONE :=
      {|
        cone_morph := Trans (iso_morphism (HLRKE_Iso hlrke)) Cn Cn
      |}.

    Next Obligation.
    Proof.
      set (W :=
             f_equal (
                 fun w :
                       (((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func _))
                             ∘ (Left_Functor_Extender p D)^op)
                         –≻ ((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ F (Hom_Func _))
                            ∘ (Left_Functor_Extender p D)^op
                         ))%nattrans =>
                   Trans w Cn
               ) (left_inverse (HLRKE_Iso hlrke))).
      cbn in W.
      match goal with
        [|- ?A = ?B] =>
        match type of W with
          ?X = _ =>
          cut (X A = X B); simpl;
            [rewrite (equal_f W A); rewrite (equal_f W B); trivial|clear W]
        end
      end.
      apply f_equal.
      set (M :=
             equal_f
               (@Trans_com _ _ _ _
                           (iso_morphism (HLRKE_Iso hlrke))
                           hlrke
                           Cn
                           (Trans (iso_morphism (HLRKE_Iso hlrke)) Cn Cn)
               )
               (Trans (inverse_morphism (HLRKE_Iso hlrke))
                      hlrke (NatTrans_id hlrke))).
      cbn in M.
      repeat rewrite NatTrans_id_unit_left in M.
      rewrite M; clear M.
      apply NatTrans_eq_simplify; extensionality x; cbn.
      cbn_rewrite (
          f_equal
            (fun w :
                   ((@Fix_Bi_Func_2 _ (Func_Cat _ _) _ hlrke (Hom_Func _))
                      –≻ (@Fix_Bi_Func_2 _ (Func_Cat _ _) _ hlrke (Hom_Func _))
                   )%nattrans
             => Trans w hlrke (NatTrans_id _)
            )
            (right_inverse (HLRKE_Iso hlrke))
        ).
      cbn; auto.
    Qed.

  End Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone.

  (** We show that any two cone morphs to TCONE (see above) are equal. *)
  Section
    Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique.
    Context {Cn : LoKan_Cone p F} (h h' : LoKan_Cone_Morph Cn TCONE).

    Theorem
      Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique
      : h = h' :> (_ –≻ _)%nattrans.
    Proof.
      set (Mh :=
             equal_f
               (@Trans_com _ _ _ _ (iso_morphism (HLRKE_Iso hlrke)) hlrke Cn h)
               (Trans (inverse_morphism (HLRKE_Iso hlrke))
                      hlrke (NatTrans_id hlrke))
          ).
      set (Mh' :=
             equal_f
               (@Trans_com _ _ _ _ (iso_morphism (HLRKE_Iso hlrke)) hlrke Cn h')
               (Trans (inverse_morphism
                         (HLRKE_Iso hlrke)) hlrke (NatTrans_id hlrke))
          ).
      cbn in Mh, Mh'.
      cbn_rewrite ((f_equal
                      (fun w :
                           ((@Fix_Bi_Func_2
                               _ (Func_Cat _ _) _ hlrke (Hom_Func _))
                              –≻ (@Fix_Bi_Func_2
                                    _ (Func_Cat _ _) _ hlrke (Hom_Func _))
                           )%nattrans
                       => Trans w hlrke (NatTrans_id _))
                      (right_inverse (HLRKE_Iso hlrke)))) in Mh Mh'.
      repeat rewrite NatTrans_id_unit_left in Mh, Mh'.
      destruct Mh; destruct Mh'.
      apply f_equal.
      etransitivity;
        [symmetry; apply (cone_morph_com h) | apply (cone_morph_com h')].
    Qed.

  End
    Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique.

  (** Conversion from Hom_Local_Right_KanExt to Local_Right_KanExt. *)
  Definition Hom_Local_Right_KanExt_to_Local_Right_KanExt :
    Local_Right_KanExt p F :=
    {|
      LRKE := TCONE;
      LRKE_morph_ex :=
        Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone;
      LRKE_morph_unique :=
        @Hom_Local_Right_KanExt_to_Local_Right_KanExt_Morph_to_Terminal_Cone_unique
    |}.

End Hom_Local_Right_KanExt_to_Local_Right_KanExt.
