From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main Functor.Representable.Hom_Func.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Ext_Cons.Arrow.
From Categories Require Import Coq_Cats.Type_Cat.Card_Restriction.
From Categories Require Import Limits.Limit.
From Categories Require Import KanExt.Pointwise.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import NatTrans.Main.
From Categories Require Import Cat.Terminal.
From Categories Require Import Functor.Representable.Representable.

Local Open Scope functor_scope.

Local Notation NID := NatTrans_id (only parsing).
Local Notation FCAT := Func_Cat (only parsing).


(** Limits – as local kan extensions – are pointwise. *)
Section Rep_Preserve_Limits.
  Context {J C : Category} (D : J –≻ C) (x : C).

  Local Notation REPx :=
    (@Fix_Bi_Func_1 (C^op) _ _ x (Hom_Func C)) (only parsing).

  Local Notation REPxComp U := (REPx ∘ U)%functor (only parsing).
  
  Section Rep_Preserve_Limits_Cone_Cov.
    Context (Cn : Cone D).

    Definition Rep_Preserve_Limits_Cone_Cov : Cone (REPxComp D) :=
      {|
        cone_apex := (REPxComp Cn);
        cone_edge := (((NID REPx) ∘_h (cone_edge Cn))
                        ∘ (NatTrans_Functor_assoc _ _ _))%nattrans
      |}.

  End Rep_Preserve_Limits_Cone_Cov.

  Local Notation LPCC := Rep_Preserve_Limits_Cone_Cov.

  Section Rep_Preserve_Limits_Cone_Cov_Back.
    Context (Cn : Cone (REPxComp D)) (w : (Cn _o tt)%object).

    Program Definition Rep_Preserve_Limits_Cone_Cov_Back : Cone D :=
      {|
        cone_apex := Const_Func Discr.SingletonCat x;
        cone_edge :=  {|Trans := fun c => Trans (cone_edge Cn) c w |}
      |}.

    Next Obligation.
    Proof.
      set (W := equal_f (@Trans_com _ _ _ _ Cn c c' h) w);
      cbn in W; rewrite From_Term_Cat in W.
      auto.
    Qed.

    Next Obligation.
    Proof.
      symmetry.
      apply Rep_Preserve_Limits_Cone_Cov_Back_obligation_1.
    Qed.      

  End Rep_Preserve_Limits_Cone_Cov_Back.

  Local Notation LPCCB := Rep_Preserve_Limits_Cone_Cov_Back.
  
  Section Rep_Preserve_Limits_Cone_Morph_Cov.
    Context {Cn Cn' : Cone D} (h : Cone_Morph D Cn Cn').

    Program Definition Rep_Preserve_Limits_Cone_Morph_Cov :
      Cone_Morph (REPxComp D) (LPCC Cn) (LPCC Cn') :=
      {|
        cone_morph := ((NID REPx) ∘_h (cone_morph h))%nattrans
      |}.

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality f; extensionality y.
      cbn in *.
      cbn_rewrite (
          f_equal
            (fun w : ((Cn ∘ (Functor_To_1_Cat J)) –≻ D)%nattrans => Trans w f)
            (cone_morph_com h)
        ).
      auto.
    Qed.
      
  End Rep_Preserve_Limits_Cone_Morph_Cov.

  Local Notation LPCHC := Rep_Preserve_Limits_Cone_Morph_Cov.
  
  Context (L : Limit D).

  Section Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit.
    Context (Cn : Cone (REPxComp D)).

    Program Definition Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit
      : Cone_Morph (REPxComp D) Cn (LPCC L) :=
      {|
        cone_morph :=
          {|
            Trans :=
              fun c w =>
                match c as u return
                      (Cn _o u)%object → (x –≻ (L _o u))%object%morphism
                with
                  tt => fun w => Trans (LRKE_morph_ex L (LPCCB Cn w)) tt
                end w
          |}
      |}.

    Next Obligation.
    Proof.
      extensionality z.
      destruct c.
      destruct c'.
      destruct h.
      repeat rewrite From_Term_Cat; auto.
    Qed.      

    Next Obligation.
    Proof.
      symmetry.
      apply Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit_obligation_1.
    Qed.    

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality c; extensionality w.
      set (W :=
             f_equal
               (fun m : (((LPCCB Cn w)
                          ∘ (Functor_To_1_Cat J)) –≻ D)%nattrans => Trans m c)
               (cone_morph_com (LRKE_morph_ex L (LPCCB Cn w)))
          ).
      cbn in *.
      auto.
    Qed.      

  End Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit.

  Local Notation LPCMTL := Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit.
  
  Section Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit.
    Context {Cn : Cone (REPxComp D)}
            (h : Cone_Morph (REPxComp D) Cn (LPCC L))
            (w : (Cn _o tt)%object)
    .

    Program Definition
            Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit
      : Cone_Morph D (LPCCB Cn w) L :=
      {|
        cone_morph :=
          {|
            Trans :=
              fun c =>
                match c as u return (x –≻ (L _o u))%object%morphism with
                  tt => Trans h tt w
                end
          |}
      |}.

    Next Obligation.
    Proof.
      destruct c; destruct c'.
      repeat rewrite From_Term_Cat; auto.
    Qed.      

    Next Obligation.
    Proof.
      symmetry.
      apply Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit_obligation_1.
    Qed.    

    Next Obligation.
    Proof.
      apply NatTrans_eq_simplify; extensionality c.
      set (W :=
             f_equal
               (fun m : ((Cn ∘ (Functor_To_1_Cat J)) –≻ (REPxComp D))%nattrans
                => Trans m c w)
               (cone_morph_com h)
          ).
      cbn in *.
      auto.
    Qed.      

  End Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit.

  Local Notation LPCMTLTL :=
    Rep_Preserve_Limits_Cone_Morph_to_LPCC_Limit_TO_Cone_Morph_to_Limit.
  
  Program Definition Rep_Preserve_Limits : Limit (REPxComp D) :=
    {|
      LRKE := LPCC L;
      LRKE_morph_ex := fun Cn => LPCMTL Cn
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify; extensionality z;
    extensionality w; destruct z; cbn in *.
    apply
      (
        f_equal
          (fun m :  ((LPCCB Cn w) –≻ L)%nattrans => Trans m tt)
          (LRKE_morph_unique L _ (LPCMTLTL h w)(LPCMTLTL h' w))
      ).
  Qed.

End Rep_Preserve_Limits.

Section Limits_Pointwise.
  Context {J C : Category} {D : J –≻ C} (L : Limit D).

  Definition Limits_Pointwise : Pointwise_LRKE L :=
    fun G GR =>
      (
        Iso_Local_Right_KanExt
          ((representation_Iso GR)⁻¹ ∘_h (NatTrans_id_Iso L))%natiso
          (
            Local_Right_KanExt_is_Local_Right_KanExt
              (Functor_To_1_Cat J)
              (Functor_compose D G)
              (
                @Local_Right_KanExt_Iso
                  _
                  _
                  (Functor_To_1_Cat J)
                  _
                  _
                  _
                  ((representation_Iso GR) ∘_h (NatTrans_id_Iso D))%natiso
                  (Rep_Preserve_Limits D (representer GR) L)
              )
          )
      ).
  
End Limits_Pointwise.  
    
    
Section CoLimits_Pointwise.
  Context {J C : Category} {D : J –≻ C} (L : CoLimit D).

  Definition CoLimits_Pointwise : Pointwise_LRKE L :=
    fun G GR => Limits_Pointwise L G GR.

End CoLimits_Pointwise.
