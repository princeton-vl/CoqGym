From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.

From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Basic_Cons.Product.

From Categories Require Import NatTrans.NatTrans NatTrans.NatIso.
From Categories Require Import Yoneda.Yoneda.

(** 1 × a ≃ a. where 1 is the terminal object. *)
Section Term_Prod.
  Context {C : Category} {term : (𝟙_ C)%object} {CHP : Has_Products C}.

  Local Notation "1" := (terminal term) : object_scope.
  
  Local Notation "a × b" := (CHP a b) : object_scope.

  (** Natural transformations to be used with Yoneda. *)
  Program Definition Term_Prod_lr (a : C) :
      ((((Yoneda C) _o (a × 1))%object)
         –≻ ((Yoneda C) _o a)%object)%nattrans
    :=
      {|
        Trans := fun b f => @compose C _ _ _ f (@Pi_1 _ _ _ (CHP a term))
      |}.

  Program Definition Term_Prod_rl (a : C) :
    ((((Yoneda C) _o a)%object)
       –≻ ((Yoneda C) _o (a × 1))%object)%nattrans
    :=
      {|
        Trans := fun b f =>  @Prod_morph_ex C _ _ _ _ f (@t_morph C _ b)
      |}.
  
  Next Obligation. (* Trans_com *)
  Proof.
    extensionality g.
    eapply Prod_morph_unique; simpl_ids.
    apply Prod_morph_com_1.
    apply Prod_morph_com_2.
    rewrite <- assoc.
    rewrite Prod_morph_com_1; trivial.
    rewrite <- assoc.
    rewrite Prod_morph_com_2.
    apply t_morph_unique.
  Qed.

  Next Obligation. (* Trans_com *)
  Proof.
    symmetry.
    apply Term_Prod_rl_obligation_1.
  Qed.
  
  Theorem Term_Prod (a : C) : (((×ᶠⁿᶜ C) _o (a, 1)%object) ≃ a)%isomorphism.
  Proof.
    Yoneda.
    apply (NatIso _ _ (Term_Prod_lr a) (Term_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      simpl_ids.
      apply Prod_morph_com_1.
    }
    {
      intros c.
      extensionality g; simpl.
      simpl_ids.
      eapply Prod_morph_unique.
      apply Prod_morph_com_1.
      apply Prod_morph_com_2.
      trivial.
      apply t_morph_unique.
    }
  Qed.

End Term_Prod.
