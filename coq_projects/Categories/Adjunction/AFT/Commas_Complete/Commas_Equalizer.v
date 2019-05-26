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
equalizers. *)
Section Commas_Equalizer.
  Context
    {C D : Category}
    {CC : Complete C}
    {G : (C –≻ D)%functor}
    (GCont : Continuous CC G)
    (x : D)
  .

  Context {a b : (Comma (Func_From_SingletonCat x) G)} (f g: (a –≻ b)%morphism).
  

  Local Hint Extern 1 => match goal with [x : bool |- _] => destruct x end.
  Local Hint Extern 1 => match goal with [x : unit |- _] => destruct x end.
  Local Hint Extern 1 => apply Comma_Hom_eq_simplify.
  Local Hint Extern 1 => progress cbn in *.
  Local Hint Extern 1 => rewrite From_Term_Cat.
  
  Local Obligation Tactic := basic_simpl; auto 10.
  
  Definition G_Eq_producing_Func_CMH_right_Limit :=
    is_Cone_Local_Right_KanExt_Local_Right_KanExt
      _
      _
      (GCont _ (Equalizer_Producing_Func (CMH_right f) (CMH_right g)))
  .

  Definition Eq_CMH_right_f_CMH_right_g :
    Equalizer (CMH_right f) (CMH_right g)
    :=
      Equalizer_as_Limit
        _ _ (LimitOf (Equalizer_Producing_Func (CMH_right f) (CMH_right g)))
  .

  Program Definition
          G_Eq_producing_Func_CMH_right_Eq_producing_Func_G_CMH_right_Iso :
    (
      ((Equalizer_Producing_Func
          (G _a (CMH_right f)) (G _a (CMH_right g)))%morphism)
        ≃
        (G ∘ Equalizer_Producing_Func (CMH_right f) (CMH_right g))%functor
    )%natiso
    :=
      {|
        iso_morphism :=
          {|
            Trans := fun c => _
          |};
        inverse_morphism :=
          {|
            Trans := fun c => _
          |}
      |}
  .

  Next Obligation.
  Proof.
    destruct c; exact id.
  Defined.

  Next Obligation.
  Proof.      
    destruct c; exact id.
  Defined.
  
  Definition Eq_producing_Func_G_CMH_right_Limit :
    Limit (Equalizer_Producing_Func
             (G _a (CMH_right f)) (G _a (CMH_right g)))%morphism
    :=
      Local_Right_KanExt_Iso
        G_Eq_producing_Func_CMH_right_Eq_producing_Func_G_CMH_right_Iso
        G_Eq_producing_Func_CMH_right_Limit
  .

  Definition Eq_G_CMH_right :
    Equalizer (G _a (CMH_right f))%morphism (G _a (CMH_right g))%morphism
    :=
      Equalizer_as_Limit _ _ Eq_producing_Func_G_CMH_right_Limit.

  Theorem CMO_hom_a_equalizes :
    ((G _a (CMH_right f)) ∘ (CMO_hom a))%morphism
    = ((G _a (CMH_right g)) ∘ (CMO_hom a))%morphism
  .
  Proof.
    rewrite (CMH_com f).
    rewrite (CMH_com g).
    destruct (CMH_left f); destruct (CMH_left g).
    trivial.
  Qed.      

  Program Definition Comma_Equalizer_Obj : Comma (Func_From_SingletonCat x) G :=
    {|
      CMO_src := tt;
      CMO_trg := equalizer _ _ Eq_CMH_right_f_CMH_right_g;
      CMO_hom :=
        equalizer_morph_ex Eq_G_CMH_right CMO_hom_a_equalizes
    |}
  .

  Program Definition Comma_Equalizer :
    Equalizer f g
    :=
      {|
        equalizer := Comma_Equalizer_Obj;
        equalizer_morph :=
          {|
            CMH_left := tt;
            CMH_right := (equalizer_morph Eq_CMH_right_f_CMH_right_g)
          |};
        equalizer_morph_ex :=
          fun e eqm eqmc =>
            {|
              CMH_left := tt;
              CMH_right :=
                equalizer_morph_ex
                  Eq_CMH_right_f_CMH_right_g
                  (f_equal CMH_right eqmc)
            |}
      |}
  .

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    etransitivity;
    [|
     etransitivity;
       [apply (equalizer_morph_ex_com Eq_G_CMH_right CMO_hom_a_equalizes)|]
    ].
    {
      cbn -[equalizer_morph_ex].
      simpl_ids.
      rewrite From_Term_Cat.
      rewrite F_id.
      simpl_ids.
      trivial.
    }
    {
      auto.
    }
  Qed.

  Next Obligation.
  Proof.    
    apply Comma_Hom_eq_simplify; cbn -[equalizer_morph]; auto.
    apply (equalizer_morph_com Eq_CMH_right_f_CMH_right_g).
  Qed.

  Next Obligation.
  Proof.
    intros e eqm eqmc.
    unfold Comma_Equalizer_Obj.
    cbn [CMO_hom].
    assert
      (H :
         ((G _a (CMH_right f)) ∘ (G _a (CMH_right eqm)))%morphism
         =
         ((G _a (CMH_right g)) ∘ (G _a (CMH_right eqm)))%morphism
      )
      by
        (repeat rewrite <- F_compose;
          cbn_rewrite (f_equal CMH_right eqmc); trivial)
    .
    match goal with
      [|- (?A ∘ _)%morphism = _] =>
      replace A with (equalizer_morph_ex Eq_G_CMH_right H)
    end.
    {
      apply (
          @equalizer_morph_unique
            _
            _
            _
            _
            _
            Eq_G_CMH_right
            _
            _
            CMO_hom_a_equalizes
        ).
      {
        rewrite assoc_sym.
        rewrite (equalizer_morph_ex_com Eq_G_CMH_right H).
        etransitivity;[apply (CMH_com eqm)|]; auto.
      }
      {
        cbn [FA Func_From_SingletonCat].
        simpl_ids.
        apply (equalizer_morph_ex_com Eq_G_CMH_right CMO_hom_a_equalizes).
      }
    }
    {
      apply (
          @equalizer_morph_unique
            _
            _
            _
            _
            _
            Eq_G_CMH_right
            _
            _
            H
        ).
      {
        rewrite (equalizer_morph_ex_com Eq_G_CMH_right H); trivial.
      }        
      {
        etransitivity;
        [
        | etransitivity;
          [
            apply
              (
                f_equal
                  (fun w => (G _a w)%morphism)
                  (equalizer_morph_ex_com
                     Eq_CMH_right_f_CMH_right_g (f_equal CMH_right eqmc)
                  )
              )
          |
          ]
        ]; trivial.
        cbn -[equalizer_morph_ex].
        simpl_ids.
        rewrite From_Term_Cat.
        rewrite F_id.
        simpl_ids.
        rewrite <- F_compose.
        trivial.
      }      
    }      
  Qed.

  Next Obligation.
  Proof.
    intros e eqm eqmc.
    apply Comma_Hom_eq_simplify.
    {
      cbn.
      match goal with
        [|- _ = ?A] => destruct A; trivial
      end.
    }
    {
      cbn -[equalizer_morph equalizer_morph_ex].
      apply (equalizer_morph_ex_com Eq_CMH_right_f_CMH_right_g).
    }
  Qed.

  Next Obligation.
  Proof.
    intros e eqm eqmc u u' H1 H2.
    apply Comma_Hom_eq_simplify.
    {
      cbn.
      match goal with
        [|- ?A = ?B] => destruct A; destruct B; trivial
      end.
    }
    {
      apply (
          @equalizer_morph_unique
            _
            _
            _
            _
            _
            Eq_CMH_right_f_CMH_right_g
            _
            _
            (f_equal CMH_right eqmc)
        ).
      + apply (f_equal CMH_right H1).
      + apply (f_equal CMH_right H2).
    }
  Qed.      

End Commas_Equalizer.
