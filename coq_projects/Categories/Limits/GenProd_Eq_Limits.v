From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Ext_Cons.Arrow.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Basic_Cons.Equalizer.
From Categories Require Import Basic_Cons.Facts.Equalizer_Monic.
From Categories Require Import Coq_Cats.Type_Cat.Card_Restriction.
From Categories Require Import Archetypal.Discr.Discr Archetypal.Discr.NatFacts.

From Categories Require Import Limits.GenProd_GenSum.
From Categories Require Import Limits.Limit.

Local Open Scope functor_scope.

Section GenProd_Eq_Complete.
  Context {C : Category}.

  Local Ltac ElimUnit := repeat match goal with [H : unit |- _] => destruct H end.

  Section GenProd_Eq_Limits.
    Context {J : Category}.

    Context {OProd : ∀ (map : J → C), (Π map)%object}
            {HProd : ∀ (map : (Arrow J) → C), (Π map)%object}
            {Eqs : Has_Equalizers C}
    .

    Section Limits_Exist.
      Context (D : J –≻ C).

      Local Notation DTarg := (fun f => (D _o (Targ f))%object) (only parsing).
      Local Notation DF := Discr_Func (only parsing).
      Local Notation OPR := (OProd (D _o)%object) (only parsing).
      Local Notation HPR := (HProd DTarg) (only parsing).

      Program Definition Projs_Cone : Cone (DF DTarg) :=
        {|
          cone_apex := Const_Func 1 (OPR _o tt);
          cone_edge := {|Trans := fun f => Trans (cone_edge OPR) (Targ f)|}
        |}.

      Definition Projs : (OPR –≻ HPR)%morphism :=
        Trans (LRKE_morph_ex HPR Projs_Cone) tt.

      Program Definition D_imgs_Cone : Cone (DF DTarg) :=
        {|
          cone_apex := Const_Func 1 (OPR _o tt);
          cone_edge :=
            {|
              Trans :=
                fun f =>
                  (D _a (Arr f) ∘ (Trans (cone_edge OPR) (Orig f)))%morphism
            |}
        |}.

      Definition D_imgs : (OPR –≻ HPR)%morphism :=
        Trans (LRKE_morph_ex HPR D_imgs_Cone) tt.

      Program Definition Lim_Cone : Cone D :=
        {|
          cone_apex := Const_Func 1 (Eqs _ _ Projs D_imgs);
          cone_edge :=
            {|Trans :=
                fun d => ((Trans (cone_edge OPR) d)
                         ∘ (equalizer_morph (Eqs _ _ Projs D_imgs)))%morphism
            |}
        |}.

      Next Obligation.
      Proof.
        simpl_ids.
        set (W :=
               f_equal
                 (fun t :
                        (((Const_Func 1 (((OProd (D _o)) _o) tt)%object)
                             ∘ (Functor_To_1_Cat (Discr_Cat (Arrow J))))
                          –≻ (DF DTarg))%nattrans
                  =>
                    ((Trans t {|Arr := h|})
                       ∘ (equalizer_morph (Eqs _ _ Projs D_imgs)))%morphism
                 )
                 (cone_morph_com (LRKE_morph_ex HPR D_imgs_Cone))
            ).
        set (W' :=
               f_equal
                 (fun t :
                        (((Const_Func 1 (((OProd (D _o)) _o) tt)%object)
                             ∘ (Functor_To_1_Cat (Discr_Cat (Arrow J))))
                          –≻ (DF DTarg))%nattrans
                  =>
                    (Trans t {|Arr := h|}
                           ∘ (equalizer_morph (Eqs _ _ Projs D_imgs)))%morphism
                 )
                 (cone_morph_com (LRKE_morph_ex HPR Projs_Cone))
            ).
        clearbody W W'.
        rewrite (assoc_sym _ _ ((D _a) h)).
        cbn in *.
        fold D_imgs in W.
        fold Projs in W'.
        rewrite W'.
        etransitivity; [|symmetry; apply W].
        clear W W'.
        repeat rewrite assoc.
        apply (
            f_equal
              (fun f =>
                 compose f
                         (Trans
                            (HProd (fun f : Arrow J => (D _o)%object (Targ f)))
                            {| Arr := h |}
                         )
              )
          ).
        apply (
            f_equal (
                fun f =>
                  compose f
                          (((HProd (fun f : Arrow J =>
                                      (D _o)%object (Targ f))) _a) tt)
              )
          ).
        apply equalizer_morph_com.
      Qed.        

      Next Obligation.
      Proof.
        symmetry.
        apply Lim_Cone_obligation_1.
      Qed.

      Section Every_Cone_Equalizes.
        Context (Cn : Cone D).

        Local Hint Extern 1 => progress cbn.

        Program Definition Cone_to_DF_DCone : Cone (DF (D _o)%object) :=
          {|
            cone_apex := Cn;
            cone_edge :=
              @NatTrans_compose
                _ _
                (Cn ∘ (Functor_To_1_Cat (Discr_Cat J)))
                (Discr_Func ((Cn ∘ (Functor_To_1_Cat J))%functor _o)%object) _
                {|Trans := fun _ => id |} (Discretize (cone_edge Cn))
          |}.

        Definition From_Cone_to_OPR : (Cn –≻ OPR)%morphism :=
          Trans (LRKE_morph_ex OPR Cone_to_DF_DCone) tt.

        Program Definition Cone_to_DF_DTrag_Cone : Cone (DF DTarg) :=
          {|
            cone_apex := Cn;
            cone_edge := {|Trans :=
                             fun c => Trans (Discretize (cone_edge Cn)) (Targ c)|}
          |}.

        Program Definition Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_1 :
          Cone_Morph _ Cone_to_DF_DTrag_Cone HPR :=
          {|
            cone_morph :=
              {|Trans :=
                  fun f =>
                    match f as u return (((Cn _o) u)%object –≻ (_ u))%morphism
                    with
                    | tt => (Projs ∘ From_Cone_to_OPR)%morphism
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          ElimUnit.
          do 2 rewrite From_Term_Cat.
          auto.
        Qed.

        Next Obligation.
        Proof.
          symmetry.
          apply Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_1_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x; cbn.
          unfold Projs, From_Cone_to_OPR.
          set (H :=
                 f_equal
                   (fun w :
                        ((Projs_Cone
                            ∘ (Functor_To_1_Cat (Discr_Cat (Arrow J)))
                         ) –≻ (DF DTarg))%nattrans
                    =>
                      (
                        (Trans w x)
                          ∘ (Trans
                               (LRKE_morph_ex
                                  (OProd (D _o)%object) Cone_to_DF_DCone) tt)
                      )%morphism
                   )
                   (
                     cone_morph_com
                       (
                         LRKE_morph_ex
                           (HProd (fun f : Arrow J => (D _o)%object (Targ f)))
                           Projs_Cone
                       )
                   )
              );
            clearbody H; cbn in H.
          repeat rewrite assoc_sym in H.
          repeat rewrite assoc_sym.
          etransitivity; [|apply H]; clear H.
          set (H :=
                 f_equal
                   (
                     fun w :
                         ((Cone_to_DF_DCone
                             ∘ (Functor_To_1_Cat (Discr_Cat J))
                          ) –≻ (DF (D _o)%object))%nattrans
                     =>
                       Trans w (Targ x)
                   )
                   (cone_morph_com (LRKE_morph_ex
                                      (OProd (D _o)%object) Cone_to_DF_DCone))
              ).
          cbn in *.
          rewrite From_Term_Cat in H; simpl_ids in H.
          trivial.
        Qed.

        Program Definition Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_2 :
          Cone_Morph _ Cone_to_DF_DTrag_Cone HPR :=
          {|
            cone_morph :=
              {|Trans :=
                  fun f =>
                    match f as u return (((Cn _o)%object u) –≻ (_ u))%morphism
                    with
                    | tt => (D_imgs ∘ From_Cone_to_OPR)%morphism
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          ElimUnit.
          do 2 rewrite From_Term_Cat; simpl_ids; trivial.
        Qed.

        Next Obligation.
        Proof.
          symmetry.
          apply Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_2_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x.
          cbn.
          unfold D_imgs, From_Cone_to_OPR.
          set (H :=
                 f_equal
                   (
                     fun w :
                         ((D_imgs_Cone
                             ∘ (Functor_To_1_Cat (Discr_Cat (Arrow J)))
                          ) –≻ (DF DTarg))%nattrans
                     =>
                       (
                         (Trans w x)
                           ∘ (Trans
                                (LRKE_morph_ex
                                   (OProd (D _o)%object) Cone_to_DF_DCone)tt)
                       )%morphism
                   )
                   (
                     cone_morph_com
                       (LRKE_morph_ex
                          (HProd (fun f : Arrow J =>
                                    (D _o)%object (Targ f))) D_imgs_Cone )
                   )
              );
            clearbody H; cbn in H.
          repeat rewrite assoc_sym in H.
          repeat rewrite assoc_sym.
          etransitivity; [|apply H]; clear H.
          set (H :=
                 f_equal
                   (
                     fun w :
                         ((Cone_to_DF_DCone
                             ∘ (Functor_To_1_Cat (Discr_Cat J))
                          ) –≻ (DF (D _o)%object))%nattrans
                     =>
                       (((D _a) (Arr x)) ∘ (Trans w (Orig x)))%morphism
                   )
                   (cone_morph_com
                      (LRKE_morph_ex (OProd (D _o)%object) Cone_to_DF_DCone))
              );
            clearbody H; cbn in H.
          rewrite From_Term_Cat in H; simpl_ids in H.
          repeat rewrite assoc_sym in H.
          repeat rewrite assoc_sym.
          etransitivity; [|apply H]; clear H.
          cbn_rewrite <- (@Trans_com _ _ _ _ Cn).
          rewrite From_Term_Cat; auto.
        Qed.

        Lemma From_Cone_to_Obj_Prod_Equalizes :
          (Projs ∘ From_Cone_to_OPR = D_imgs ∘ From_Cone_to_OPR)%morphism.
        Proof.
          match goal with
            [|- ?A = ?B] =>
            change A with
            (Trans Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_1 tt);
              change B with
              (Trans Cone_Morph_From_Cone_to_DF_DTrag_Cone_to_HPR_2 tt)
          end.
          match goal with
            [|- Trans ?A tt = Trans ?B tt] =>
            assert (A = B) as Heq; [|rewrite Heq]; trivial
          end.
          apply (LRKE_morph_unique HPR).
        Qed.

        Definition From_Cone_to_Lim_Cone : (Cn –≻ Lim_Cone)%morphism :=
          equalizer_morph_ex _  From_Cone_to_Obj_Prod_Equalizes.

        Program Definition Cone_Morph_to_Lim_Cone : Cone_Morph D Cn Lim_Cone :=
          {|
            cone_morph :=
              {|
                Trans :=
                  fun c =>
                    match c as u return ((Cn _o u)%object –≻ _)%morphism with
                      tt => From_Cone_to_Lim_Cone
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          ElimUnit.
          rewrite From_Term_Cat; auto.
        Qed.

        Next Obligation.
          symmetry.
          apply Cone_Morph_to_Lim_Cone_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x.
          unfold From_Cone_to_Lim_Cone.
          cbn in *.
          set (H :=
                 equalizer_morph_ex_com
                   (Eqs _ _ Projs D_imgs)
                   From_Cone_to_Obj_Prod_Equalizes
              );
            clearbody H; cbn in H.
          simpl_ids.
          rewrite assoc.
          match goal with
            [|- _ = (?A ∘ ?B)%morphism] =>
            replace B with From_Cone_to_OPR
          end.
          clear H.
          unfold From_Cone_to_OPR.
          set (H :=
                 f_equal
                   (
                     fun w :
                         ((Cone_to_DF_DCone ∘ (Functor_To_1_Cat (Discr_Cat J))
                          ) –≻ (DF (D _o)%object))%nattrans
                     =>
                       Trans w x
                   )
                   (cone_morph_com (LRKE_morph_ex
                                      (OProd (D _o)%object) Cone_to_DF_DCone))
              ).
          cbn in H.
          rewrite From_Term_Cat in H; simpl_ids in H.
          trivial.
        Qed.

      End Every_Cone_Equalizes.

      Section Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR.
        Context {Cn : Cone D} (h : Cone_Morph _ Cn Lim_Cone).

        Program Definition Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR :
          Cone_Morph _ (Cone_to_DF_DCone Cn) OPR :=
          {|
            cone_morph :=
              {|
                Trans :=
                  fun c =>
                    match c as u return
                          (((Cn _o) u)
                             –≻ (((OProd (D _o)) _o) u))%object%morphism
                    with
                    | tt => (equalizer_morph (Eqs _ _ Projs D_imgs)
                                            ∘ Trans h tt)%morphism
                    end
              |}
          |}.

        Next Obligation.
        Proof.
          ElimUnit.
          rewrite From_Term_Cat; auto.
        Qed.

        Next Obligation.
        Proof.
          symmetry.
          apply Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR_obligation_1.
        Qed.

        Next Obligation.
        Proof.
          apply NatTrans_eq_simplify.
          extensionality x.
          cbn.
          set (H :=
                 f_equal
                   (fun w : ((Cn ∘ (Functor_To_1_Cat J)) –≻ D)%nattrans =>
                      Trans w x)
                   (cone_morph_com h)
              ).
          cbn in H.
          simpl_ids in H.
          rewrite From_Term_Cat; simpl_ids.
          rewrite assoc in H.
          trivial.
        Qed.

      End Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR.

      Local Notation CMCOPR :=
        Cone_Morph_to_Lim_Cone_Cone_Morph_to_OPR (only parsing).

      Program Definition Lim_Cone_is_Limit : Limit D :=
        {|
          LRKE := Lim_Cone;
          LRKE_morph_ex := Cone_Morph_to_Lim_Cone
        |}.

      Next Obligation.
      Proof.
        set (H := LRKE_morph_unique
                    (OProd (D _o)%object) _ (CMCOPR h) (CMCOPR h')).
        apply (
            f_equal
              (fun w : ((Cone_to_DF_DCone Cn) –≻ (OProd (D _o)%object))%nattrans =>
                 Trans w tt)
          ) in H.
        cbn in H.
        apply NatTrans_eq_simplify.
        extensionality x; destruct x.
        apply (@mono_morphism_monomorphic
                 _ _ _ (@Equalizer_Monic _ _ _ _ _ (Eqs _ _ Projs D_imgs))).
        trivial.
      Qed.

    End Limits_Exist.
  End GenProd_Eq_Limits.

  Section Restricted_Limits.
    Context (P : Card_Restriction)
            {CHRP : ∀ (A : Type) (map : A → C), (P A) → (Π map)%object}
            {HE : Has_Equalizers C}
    .

    Definition Restr_GenProd_Eq_Restr_Limits : Has_Restr_Limits C P :=
      fun J D PJ PA =>
        @Lim_Cone_is_Limit
          J
          (fun map => CHRP J map PJ)
          (fun map => CHRP (Arrow J) map PA)
          HE
          D
    .

  End Restricted_Limits.

  Section Complete.
    Context {CHAP : ∀ (A : Type) (map : A → C), (Π map)%object}
            {HE : Has_Equalizers C}.

    Definition GenProd_Eq_Complete : Complete C :=
      fun J =>
        Local_to_Global_Right
          _
          _
          (fun D => @Lim_Cone_is_Limit J (CHAP J) (CHAP (Arrow J)) HE D)
    .

  End Complete.

End GenProd_Eq_Complete.

Section GenSum_CoEq_Complete.
  Context {C : Category}.

  Section GenSum_CoEq_CoLimits.
    Context {J : Category}
            {OSum : ∀ (map : J → C), (Σ map)%object}
            {HSum : ∀ (map : (Arrow J) → C), (Σ map)%object}
            {Eqs : Has_CoEqualizers C}
    .

    Section Limits_Exist.
      Context (D : J –≻ C).

      Program Definition CoLim_CoCone_is_CoLimit : CoLimit D :=
        @Lim_Cone_is_Limit
          (C^op)
          (J^op)
          (fun map => GenSum_to_GenProd (OSum map))
          (fun map => GenSum_to_GenProd (GenSum_IsoType (Arrow_OP_Iso J) HSum map))
          Eqs
          (Opposite_Functor D)
      .

    End Limits_Exist.
  End GenSum_CoEq_CoLimits.

  Section Restricted_CoLimits.
    Context (P : Card_Restriction)
            {CHRP : ∀ (A : Type) (map : A → C), (P A) → (Σ map)%object}
            {HE : Has_CoEqualizers C}
    .

    Definition Restr_GenSum_CoEq_Restr_CoLimits : Has_Restr_CoLimits C P :=
      fun J D PJ PA =>
        @CoLim_CoCone_is_CoLimit
          J
          (fun map => CHRP J map PJ)
          (fun map => CHRP (Arrow J) map PA)
          HE
          D
    .

  End Restricted_CoLimits.

  Section CoComplete.
    Context {CHAP : ∀ (A : Type) (map : A → C), (Σ map)%object}
            {HE : Has_CoEqualizers C}
    .

    Definition GenSum_CoEq_CoComplete : CoComplete C :=
      fun J =>
        Local_to_Global_Left
          _
          _
          (fun D => @CoLim_CoCone_is_CoLimit J (CHAP J) (CHAP (Arrow J)) HE D)
    .

  End CoComplete.

End GenSum_CoEq_Complete.
