From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.CCC.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Exponential.
From Categories Require Import PreSheaf.PreSheaf PreSheaf.Product.
From Categories Require Import Yoneda.Yoneda.

Section Exponential.
  Context (C : Category) (F G : PShCat C).

  Local Obligation Tactic := idtac.

  (** The exponential in category of presheaves is the presheaf that maps each
      object c of C to the set of natural transformations (Y(c) × F –≻ G).
      Where Y is the Yoneda embedding, and × is the product of presheaves.

      This presheaf, maps an arrow h : c –≻ c' in C to the natural
      transformation ( morphisms in category of presheaves are natural
      transformations) that maps a natural transformation u to the natural
      transformation that maps an objet x of C to the function that given
      v : ((c' –≻ x : Cᵒᵖ) * F(x)) gives
      (Trans u x (((fst v) ∘ f)%morphism, (snd v)))
 *)
  Program Definition funspace_psh : Functor (C^op) Type_Cat :=
    {|
      FO :=
        fun x =>
          NatTrans
            (pointwise_product_psh _ ((Yoneda C _o) x)%object F)
            G;
      FA :=
        fun _ _ f u =>
          {|
            Trans :=
              fun x v => Trans u x (((fst v) ∘ f)%morphism, (snd v))
          |}
    |}.

  Next Obligation.
  Proof.
    basic_simpl.
    extensionality v.
    simpl_ids.
    set (W := equal_f (Trans_com u h) (f ∘ (fst v), snd v)%morphism).
    cbn in W.
    simpl_ids in W.
    rewrite assoc_sym.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply funspace_psh_obligation_1.
  Qed.

  Next Obligation.
  Proof.
    intros x.
    FunExt.
    apply NatTrans_eq_simplify; cbn; auto.
  Qed.

  Next Obligation.
  Proof.    
    intros a b c f g.
    FunExt.
    apply NatTrans_eq_simplify; cbn.
    FunExt.
    rewrite assoc.
    trivial.
  Qed.

  (** The evaluation morphism (natural transformation) for exponentials of
      presheaves. *)
  Program Definition PSh_Exponential_Eval :
    (pointwise_product_psh C funspace_psh F –≻ G)%nattrans
    :=
      {|
        Trans := fun x u => Trans (fst u) x (id, snd u)
      |}.

  Next Obligation.
  Proof.
    basic_simpl.
    extensionality u.
    set (W := equal_f (Trans_com (fst u) h) (id, snd u)).
    cbn in W.
    auto.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply PSh_Exponential_Eval_obligation_1.
  Qed.

  (** The currying morphism (natural transformation) for exponentials of
      presheaves. *)
  Program Definition PSh_Exponential_Curry
          (x : (C ^op –≻ Type_Cat)%functor)
          (u : (pointwise_product_psh C x F –≻ G)%nattrans)
    :
      (x –≻ funspace_psh)%nattrans
  :=
    {|
      Trans :=
        fun v m =>
          {|
            Trans :=
              fun p q =>
                Trans u p (x _a (fst q) m, snd q)%morphism
          |}
    |}.

  Next Obligation.
  Proof.
    intros x u v m c c' h.
    cbn in *.
    extensionality p.
    simpl_ids.
    cbn_rewrite (F_compose x (fst p) h).
    set (W := equal_f (Trans_com u h) ((x _a (fst p) m)%morphism, snd p)).
    cbn in W.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry; simpl.
    apply PSh_Exponential_Curry_obligation_1.
  Qed.

  Next Obligation.
  Proof.
    intros x u c c' h.
    cbn in *.
    extensionality v.
    apply NatTrans_eq_simplify.
    extensionality z; extensionality y.
    cbn in *.
    cbn_rewrite (F_compose x h (fst y)).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    symmetry; simpl.
    apply PSh_Exponential_Curry_obligation_3.
  Qed.

  (** Exponentials of presheaves. *)
  Program Definition PSh_Exponential : (F ⇑ G)%object :=
    {|
      exponential := funspace_psh;
      eval := PSh_Exponential_Eval;
      Exp_morph_ex := PSh_Exponential_Curry
    |}.

  Next Obligation.
  Proof.
    intros z f.
    apply NatTrans_eq_simplify.
    extensionality x; extensionality y.
    cbn in *.
    rewrite (F_id z).
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros z f u u' H1 H2.
    rewrite H2 in H1; clear H2.
    assert (H1' := f_equal Trans H1); clear H1.
    symmetry in H1'.
    apply NatTrans_eq_simplify.
    extensionality x; extensionality y.
    apply NatTrans_eq_simplify.
    extensionality p.
    extensionality q.
    cbn in *.
    assert (H1 := f_equal (fun w => w p (z _a (fst q) y, snd q)%morphism) H1');
      clear H1'.
    cbn in H1.
    cbn_rewrite (equal_f (Trans_com u (fst q)) y) in H1.
    cbn_rewrite (equal_f (Trans_com u' (fst q)) y) in H1.
    cbn in H1.
    auto.
  Qed.

End Exponential.

Instance PSh_Has_Exponentials (C : Category) : Has_Exponentials (PShCat C) :=
  PSh_Exponential C.
