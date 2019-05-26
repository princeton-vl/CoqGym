From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Basic_Cons.Equalizer.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.Equalizer.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import PreSheaf.PreSheaf.

Local Obligation Tactic := idtac.

Section Equalizer.
  Context (C : Category) {A B : PreSheaf C} (f g : (A –≻ B)%nattrans).

  (** The pointwise equalizer presheaf. *)
  Program Definition PSh_ptw_eq_Func : PreSheaf C :=
    {|
      FO := fun c => Type_Cat_Has_Equalizers _ _ (Trans f c) (Trans g c);
      FA := fun c c' h x => exist _ (A _a h (proj1_sig x))%morphism _
    |}.

  Next Obligation.
  Proof.
    intros c c' h x.
    basic_simpl.
    cbn_rewrite (equal_f (Trans_com f h) x1).
    cbn_rewrite (equal_f (Trans_com g h) x1).
    rewrite x2.
    trivial.
  Qed.    

  Next Obligation.
  Proof.  
    basic_simpl; FunExt; basic_simpl.
    apply sig_proof_irrelevance; cbn.
    rewrite (F_id A).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros a b c f' g'.
    FunExt; basic_simpl.
    apply sig_proof_irrelevance; cbn.
    cbn_rewrite (F_compose A f' g').
    trivial.
  Qed.

  Local Obligation Tactic := basic_simpl; auto.

  (** The equalizer morph. *)
  Program Definition PSh_ptw_eq_morph_NatTrans : NatTrans PSh_ptw_eq_Func A :=
    {|
      Trans :=
        fun c =>
          equalizer_morph
            (Type_Cat_Has_Equalizers _ _ (Trans f c) (Trans g c))
    |}.

  Local Hint Extern 1 => apply NatTrans_eq_simplify; FunExt; basic_simpl.

  Program Definition PSh_Eq : Equalizer (PShCat C) f g :=
    {|
      equalizer := PSh_ptw_eq_Func;
      equalizer_morph := PSh_ptw_eq_morph_NatTrans;
      equalizer_morph_ex :=
        fun u v H =>
          {|
            Trans := fun c x => exist _ (Trans v c x) _
          |}
    |}.

  Next Obligation.
  Proof.
    apply (f_equal (fun w :(u –≻ B)%nattrans => Trans w c x) H).
  Qed.

  Next Obligation.
  Proof.  
    FunExt.
    apply sig_proof_irrelevance; cbn.
    apply (equal_f (Trans_com v h)).
  Qed.  

  Next Obligation.
  Proof.
    symmetry.
    apply PSh_Eq_obligation_3.
  Qed.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
    intros e' eqm H1 u u' H4 H5.
    rewrite <- H5 in H4; clear H5.
    assert (H4' := f_equal Trans H4); clear H4.
    apply NatTrans_eq_simplify.
    extensionality x; extensionality y.
    apply sig_proof_irrelevance.
    apply (f_equal (fun w => w x y) H4').
  Qed.
  
End Equalizer.

Instance PSh_Has_Equalizers (C : Category) : Has_Equalizers (PShCat C)
  := fun _ _ => PSh_Eq C.

Section CoEqualizer.
  Context (C : Category) {A B : PreSheaf C} (f g : (A –≻ B)%nattrans).


  Lemma another_coequalizer
        (c c' : C)
        (h : (c' –≻ c)%morphism)
    :
      ((equalizer_morph (Type_Cat_Has_CoEqualizers _ _ (Trans f c') (Trans g c'))) ∘ (B _a h) ∘ (Trans f c))%morphism
      =
      ((equalizer_morph (Type_Cat_Has_CoEqualizers _ _ (Trans f c') (Trans g c'))) ∘ (B _a h) ∘ (Trans g c))%morphism
  .
  Proof.
    FunExt; cbn.
    cbn_rewrite <- (equal_f (Trans_com f h)).
    cbn_rewrite <- (equal_f (Trans_com g h)).
    apply (equal_f (equalizer_morph_com (Type_Cat_Has_CoEqualizers _ _ (Trans f c') (Trans g c')))).
  Qed.

  Lemma CoEq_rel_natural
        (a b : C)
        (h : (b –≻ a)%morphism)
        (x y : (B _o)%object a)
        (H : CoEq_rel (Trans f a) (Trans g a) x y)
    :
      CoEq_rel (Trans f b) (Trans g b) (B _a h x)%morphism (B _a h y)%morphism
  .
  Proof.
    cbn in *.
    induction H.
    {
      destruct H as [z [H1 H2]].
      rewrite <- H1, <- H2.
      constructor 1.
      exists ((A _a)%morphism h z); split.
      apply (equal_f (Trans_com f h)).
      apply (equal_f (Trans_com g h)).
    }
    {
      constructor 2.
    }
    {      
      constructor 3; auto.
    }      
    {
      econstructor 4; eauto.
    }
  Qed.

  Lemma equalizer_morph_com_simplified
        (a : C)
        (x y : (B _o)%object a)
        (H : CoEq_rel (Trans f a) (Trans g a) x y)
    :
      Equalizer.Type_Cat_CoEq_obligation_1 (Trans f a) (Trans g a) y =
      Equalizer.Type_Cat_CoEq_obligation_1 (Trans f a) (Trans g a) x
  .
  Proof.
    induction H; auto.
    destruct H as [z [H1 H2]].
    rewrite <- H1, <- H2.
    symmetry.
    apply (equal_f (@equalizer_morph_com _ _ _ _ _ (Type_Cat_Has_CoEqualizers _ _ (Trans f a) (Trans g a)))).
  Qed.    

  (** The pointwise equalizer presheaf. *)
  Program Definition PSh_ptw_coeq_Func : PreSheaf C :=
    {|
      FO := fun c => Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c);
      FA :=
        fun c c' h x =>
          @equalizer_morph_ex
            _
            _
            _
            _
            _
            (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))
            _
            (
              (equalizer_morph (Type_Cat_Has_CoEqualizers _ _ (Trans f c') (Trans g c')))
                ∘ (B _a h)
            )%morphism (another_coequalizer _ _ _) x
    |}.

  Next Obligation.
  Proof.
    basic_simpl.
    eapply
      (
        @equalizer_morph_unique
          _
          _
          _
          _
          _
          (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))
          _
          (equalizer_morph (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c)))
      );
      cbn; trivial.
    + apply (@equalizer_morph_com _ _ _ _ _ (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))).
    + extensionality x.
      destruct (
          (
            CoEq_Choice
              (Trans f c)
              (Trans g c)
              (
                Equalizer.Type_Cat_CoEq_obligation_1 
                  (Trans f c)
                  (Trans g c)
                  x
              )
          )
        ) as [y H].
      rewrite (F_id B).
      apply equalizer_morph_com_simplified; assumption.
  Qed.

  Next Obligation.
  Proof.
    intros a b c f' g'.
    cbn in *.
    apply
      (
        @equalizer_morph_unique
          _
          _
          _
          _
          _
          (Type_Cat_Has_CoEqualizers _ _ (Trans f a) (Trans g a))
          _
          (
            (equalizer_morph (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c)))
              ∘ (B _a (f' ∘ g'))
          )%morphism
      );
      cbn.
    {
      extensionality x.
      cbn_rewrite (F_compose B f' g').
      cbn_rewrite <- (equal_f (Trans_com f f')).
      cbn_rewrite <- (equal_f (Trans_com f g')).
      cbn_rewrite <- (equal_f (Trans_com g f')).
      cbn_rewrite <- (equal_f (Trans_com g g')).
      apply (equal_f
               (@equalizer_morph_com
                  _
                  _
                  _
                  _
                  _
                  (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))
               )
            ).
    }
    {
      extensionality x.
      destruct (
          (
            CoEq_Choice
              _
              _
              (
                Equalizer.Type_Cat_CoEq_obligation_1
                  _
                  _
                  x
              )
          )
        ) as [y H].
      cbn in *.
      apply equalizer_morph_com_simplified.
      apply CoEq_rel_natural; trivial.
    }
    {
      extensionality x.
      cbn_rewrite (F_compose B f' g').
      destruct (
          (
            CoEq_Choice
              _
              _
              (
                Equalizer.Type_Cat_CoEq_obligation_1
                  _
                  _
                  x
              )
          )
        ) as [y H].
      cbn in *.
      destruct (
          (
            CoEq_Choice
              _
              _
              (
                Equalizer.Type_Cat_CoEq_obligation_1
                  _
                  _
                  ((B _a)%morphism f' y)
              )
          )
        ) as [z H'].
      cbn in *.
      apply equalizer_morph_com_simplified.
      apply CoEq_rel_natural; trivial.
      econstructor 4; [|exact H'].
      apply CoEq_rel_natural; trivial.
    }
  Qed.

  (** The equalizer morph. *)
  Program Definition PSh_ptw_coeq_morph_NatTrans : NatTrans B PSh_ptw_coeq_Func :=
    {|
      Trans :=
        fun c =>
          equalizer_morph
            (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))
    |}.

  Next Obligation.
  Proof.
    intros c c' h.
    extensionality x.
    cbn.
    destruct (
          (
            CoEq_Choice
              _
              _
              (
                Equalizer.Type_Cat_CoEq_obligation_1
                  _
                  _
                  x
              )
          )
        ) as [z H'].
      cbn in *.
      apply equalizer_morph_com_simplified.
      apply CoEq_rel_natural; trivial.
      constructor 3; trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply PSh_ptw_coeq_morph_NatTrans_obligation_1.
  Qed.
    
(*  Local Hint Extern 1 => apply NatTrans_eq_simplify; FunExt; basic_simpl. *)

  Program Definition PSh_CoEq : CoEqualizer (PShCat C) f g :=
    {|
      equalizer := PSh_ptw_coeq_Func;
      equalizer_morph := PSh_ptw_coeq_morph_NatTrans;
      equalizer_morph_ex :=
        fun u v H =>
          {|
            Trans := fun x w => _
          |}
    |}.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality c; extensionality x.
    cbn.
    apply (equal_f
             (@equalizer_morph_com
                _
                _
                _
                _
                _
                (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))
               )
          ).
  Qed.

  Next Obligation.
  Proof.
    intros.
    destruct (CoEq_Choice _ _ w) as [z H'].
    exact (Trans v x z).
  Defined.

  Next Obligation.
  Proof.  
    intros u v H c c' h.
    extensionality w.
    unfold PSh_CoEq_obligation_2.
    cbn in *.
    destruct (CoEq_Choice _ _ w) as [z H'].
    cbn in *.
    cbn_rewrite <- (equal_f (Trans_com v h)).
    destruct (
        CoEq_Choice
          _
          _
          (
            Equalizer.Type_Cat_CoEq_obligation_1
              _
              _
              ((B _a)%morphism h z)
          )
      ) as [y H''].
    cbn in *.
    induction H'' as [l l' H''| | |]; auto.
    destruct H'' as [q [H''1 H''2]].
    rewrite <- H''1, <- H''2.
    symmetry.
    apply (f_equal (fun w : (A –≻ u)%nattrans => Trans w c' q) H).
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply PSh_CoEq_obligation_3.
  Qed.

  Next Obligation.
  Proof.
    intros e' eqm eqmc.
    apply NatTrans_eq_simplify.
    unfold PSh_CoEq_obligation_2.
    extensionality c; extensionality x.
    cbn in *.
    destruct (
        CoEq_Choice
          _
          _
          (
            Equalizer.Type_Cat_CoEq_obligation_1
              _
              _
              x
          )
      ) as [y H''].
    cbn in *.
    induction H'' as [l l' H''| | |]; auto.
    destruct H'' as [q [H''1 H''2]].
    rewrite <- H''1, <- H''2.
    symmetry.
    apply (f_equal (fun w : (A –≻ e')%nattrans => Trans w c q) eqmc).
  Qed.
    
  Next Obligation.
    intros e' eqm eqmc u u' H4 H5.
    apply NatTrans_eq_simplify.
    extensionality c.
    assert (eqmc' := f_equal (fun w : (A –≻ e')%nattrans => Trans w c) eqmc); clear eqmc.
    assert (H4' := f_equal (fun w : (B –≻ e')%nattrans=> Trans w c) H4); clear H4.
    assert (H5' := f_equal (fun w : (B –≻ e')%nattrans => Trans w c) H5); clear H5.
    apply (
        @equalizer_morph_unique
          _
          _
          _
          _
          _
          (Type_Cat_Has_CoEqualizers _ _ (Trans f c) (Trans g c))
          _
          (Trans eqm c)
      ); assumption.
  Qed.
  
End CoEqualizer.

Instance PSh_Has_CoEqualizers (C : Category) : Has_CoEqualizers (PShCat C)
  := fun _ _ => PSh_CoEq C.
