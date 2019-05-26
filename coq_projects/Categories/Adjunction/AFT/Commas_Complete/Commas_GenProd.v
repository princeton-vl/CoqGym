From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import
        Limits.Limit
        Limits.GenProd_GenSum
        Limits.GenProd_Eq_Limits
.
From Categories Require Import Functor.Functor Functor.Functor_Ops.
From Categories Require Import NatTrans.Main.
From Categories Require Import Ext_Cons.Comma.
From Categories Require Import
        Basic_Cons.Terminal
        Basic_Cons.Equalizer
        Basic_Cons.Limits
.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Cat.Terminal.

(** We show that if C is a complete category and G : C –≻ D preserves limits,
then every comma category (Comma (Func_From_SingletonCat x) G) for (x : D) has
generalized products. *)
Section Commas_GenProd.
  Context
    {C D : Category}
    {CC : Complete C}
    {G : (C –≻ D)%functor}
    (GCont : Continuous CC G)
    (x : D)
  .


  Local Hint Extern 1 => match goal with [x : unit |- _] => destruct x end.
  Local Hint Extern 1 => apply Comma_Hom_eq_simplify.
  Local Hint Extern 1 => progress cbn in *.
  Local Hint Extern 1 => rewrite From_Term_Cat.

  Local Obligation Tactic := basic_simpl; auto 10.

  Section fun_conv.
    Context {A : Type} (f : A → (Comma (Func_From_SingletonCat x) G)).

    Definition fun_conv (y : A) : C := CMO_trg (f y).

  End fun_conv.

  Context {A : Type} (f : A → (Comma (Func_From_SingletonCat x) G)).

  Definition GenProd_fun_conv : (Π (fun_conv f))%object :=
    LimitOf (Discr_Func (fun_conv f)).

  Program Definition f_Cone : Cone (G ∘ (Discr_Func (fun_conv f)))%functor
    :=
      {|
        cone_apex :=
          {|
            FO :=
              fun _ => x;
            FA := fun _ _ _ => id
          |};
        cone_edge :=
          {|
            Trans := fun c => CMO_hom (f c)
          |}
      |}.

  Definition Limit_G_fun_conv : Limit (G ∘ (Discr_Func (fun_conv f)))%functor
    :=
      is_Cone_Local_Right_KanExt_Local_Right_KanExt
        _
        _
        (GCont _ (Discr_Func (fun_conv f)))
  .

  Section Comma_GenProd_Cone.
    Local Unset Transparent Obligations.

    Program Definition Comma_GenProd_Cone : Cone (Discr_Func f) :=
      {|
        cone_apex :=
          {|
            FO :=
              fun x =>
                {|
                  CMO_src := x;
                  CMO_trg := GenProd_fun_conv;
                  CMO_hom := Trans (LRKE_morph_ex Limit_G_fun_conv f_Cone) tt
                |};
            FA :=
              fun a b h =>
                {|
                  CMH_left := h;
                  CMH_right := id
                |}
          |};
        cone_edge :=
          {|
            Trans :=
              fun c =>
                {|
                  CMH_left := tt;
                  CMH_right := Trans GenProd_fun_conv c
                |}
          |}
      |}
    .

    Next Obligation.
    Proof.
      cbn_rewrite (f_equal
                     (fun w:
                            (f_Cone ∘ Functor_To_1_Cat (Discr_Cat A)
                                    –≻ G ∘ Discr_Func (fun_conv f))%nattrans
                      => Trans w c)
                     (cone_morph_com (LRKE_morph_ex Limit_G_fun_conv f_Cone))).
      rewrite From_Term_Cat.
      rewrite F_id.
      auto.
    Qed.

  End Comma_GenProd_Cone.

  Program Definition Cone_f_Cone_fun_conv_f (Cn : Cone (Discr_Func f)) :
    Cone (Discr_Func (fun_conv f)) :=
    {|
      cone_apex :=
        {|
          FO := fun _ => CMO_trg (Cn _o tt)%object;
          FA := fun a b h => id
        |};
      cone_edge :=
        {|
          Trans := fun c => CMH_right (Trans Cn c)
        |}
    |}
  .

  Section Cone_f_Cone_Morph_from_f_Cone.
    Context (Cn : Cone (Discr_Func f)).

    Local Obligation Tactic := idtac.

    Program Definition Cone_f_Cone_Morph_from_f_Cone  :
      LoKan_Cone_Morph f_Cone Limit_G_fun_conv
      :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun c =>
                  ((G _a
                      (Trans
                         (
                           LRKE_morph_ex
                             (GenProd_fun_conv)
                             (Cone_f_Cone_fun_conv_f Cn)
                         )
                         c
                      )
                   ) ∘ (CMO_hom (Cn _o tt)))%object%morphism
            |}
        |}
    .

    Next Obligation.
    Proof.
      basic_simpl; auto 10.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Cone_f_Cone_Morph_from_f_Cone_obligation_1.
    Qed.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality z.
      cbn in *.
      simpl_ids.
      rewrite assoc_sym.
      rewrite <- F_compose.
      rewrite assoc_sym.
      rewrite <- F_compose.
      repeat rewrite assoc.
      cbn_rewrite
        <-
        (
          f_equal
            (fun w :
                   ((Cone_f_Cone_fun_conv_f Cn)
                      ∘ Functor_To_1_Cat (Discr_Cat A)
                      –≻ Discr_Func (fun_conv f))%nattrans
             => Trans w z)
            (cone_morph_com (LRKE_morph_ex (GenProd_fun_conv) (Cone_f_Cone_fun_conv_f Cn)))
        ).
      etransitivity; [|symmetry; apply (CMH_com (Trans Cn z))].
      cbn; auto.
    Qed.

  End Cone_f_Cone_Morph_from_f_Cone.

  Section Comma_GenProd_Cone_Morph_ex.
    Context (Cn : Cone (Discr_Func f)).

    Local Unset Transparent Obligations.

    Program Definition Comma_GenProd_Cone_Morph_ex
      :
        LoKan_Cone_Morph Cn Comma_GenProd_Cone
      :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun c =>
                  {|
                    CMH_left := tt;
                    CMH_right :=
                      match c as u return (CMO_trg (Cn _o u)%object –≻ _)%morphism with
                        tt =>
                        Trans
                          (LRKE_morph_ex (GenProd_fun_conv) (Cone_f_Cone_fun_conv_f Cn))
                          tt
                      end
                  |}
            |}
        |}
    .

    Next Obligation.
    Proof.
      repeat match goal with [x : unit |- _] => destruct x end.
      simpl_ids.
      apply (
          f_equal
            (fun w : (f_Cone –≻ Limit_G_fun_conv)%nattrans => Trans w tt)
            (LRKE_morph_unique
               Limit_G_fun_conv
               f_Cone
               (Cone_f_Cone_Morph_from_f_Cone Cn)
               (LRKE_morph_ex Limit_G_fun_conv f_Cone)
            )
        ).
    Qed.

    Local Obligation Tactic := idtac.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify.
      extensionality z.
      apply Comma_Hom_eq_simplify; cbn in *.
      match goal with [|- ?A = _] => destruct A; trivial end.
      simpl_ids.
      cbn_rewrite (
          f_equal
            (fun w :
                   ((Cone_f_Cone_fun_conv_f Cn)
                      ∘ Functor_To_1_Cat (Discr_Cat A)
                      –≻ Discr_Func (fun_conv f))%nattrans
             => Trans w z)
            (cone_morph_com (LRKE_morph_ex (GenProd_fun_conv) (Cone_f_Cone_fun_conv_f Cn)))
        ).
      auto.
    Qed.

  End Comma_GenProd_Cone_Morph_ex.

  Program Definition Cone_Morph_to_Comma_GenProd_Cone_TO_Cone_Morph_to_GenProd_fun_conv
          (Cn : Cone (Discr_Func f))
          (h : LoKan_Cone_Morph Cn Comma_GenProd_Cone)
    :
      LoKan_Cone_Morph (Cone_f_Cone_fun_conv_f Cn) GenProd_fun_conv
    :=
      {|
        cone_morph :=
          {|
            Trans :=
              fun c =>
                match
                  c as u
                  return
                  (
                    (CMO_trg ((Cn _o)%object tt))
                      –≻
                      (
                        (CC
                           (Discr_Cat A) _o)
                          (Discr_Func (fun_conv f)) _o)%object
                      u
                  )%morphism
                with
                | tt => CMH_right (Trans h tt)
                end
          |}
      |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality z.
    cbn.
    cbn_rewrite (
        f_equal
          (fun w :
                 ((Cn ∘ Functor_To_1_Cat (Discr_Cat A))
                    –≻
                    @Discr_Func (Comma (Func_From_SingletonCat x) G) _ f)%nattrans
           => CMH_right (Trans w z)
          )
          (cone_morph_com h)
      ).
    auto.
  Qed.

  Program Definition Comma_GenProd : (Π f)%object
    :=
      {|
        LRKE := Comma_GenProd_Cone;
        LRKE_morph_ex := Comma_GenProd_Cone_Morph_ex
      |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality z.
    destruct z.
    apply Comma_Hom_eq_simplify.
    match goal with [|- ?A = ?B] => destruct A; destruct B; trivial end.
    change (CMH_right (Trans h tt)) with
    (Trans (Cone_Morph_to_Comma_GenProd_Cone_TO_Cone_Morph_to_GenProd_fun_conv Cn h) tt).
    change (CMH_right (Trans h' tt)) with
    (Trans (Cone_Morph_to_Comma_GenProd_Cone_TO_Cone_Morph_to_GenProd_fun_conv Cn h') tt).
    match goal with
      [|- Trans ?A tt = Trans ?B tt] =>
      assert (A = B) as Heq; [|rewrite Heq]; trivial
    end.
    apply (LRKE_morph_unique GenProd_fun_conv).
  Qed.

End Commas_GenProd.
