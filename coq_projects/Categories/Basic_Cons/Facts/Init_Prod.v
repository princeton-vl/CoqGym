From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.

From Categories Require Import Basic_Cons.CCC.

From Categories Require Import NatTrans.NatTrans NatTrans.NatIso.
From Categories Require Import Yoneda.Yoneda.

(** 0 × a ≃ 0. where 0 is the initial object *)
Section Init_Prod.
  Context {C : Category} {C_CCC : CCC C} {init : (𝟘_ C)%object}.

  Local Notation "0" := (terminal init) : object_scope.
  
(*  Local Notation "a × b" := (CHP a b) : object_scope. *)

  (** Natural transformations to be used with Yoneda. *)
  
  Program Definition Init_Prod_lr a :
    (((((CoYoneda C) _o) ((×ᶠⁿᶜ C) _o (0, a)))%object)
      –≻ (((CoYoneda C) _o) 0)%object)%nattrans
    :=
      {|
        Trans := fun b f => @t_morph _ init b
      |}.

  Next Obligation.
  Proof.
    extensionality g.
    apply t_morph_unique.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Init_Prod_lr_obligation_1.
  Qed.

  Program Definition Init_Prod_rl a :
    (((((CoYoneda C) _o) 0)%object)
       –≻ (((CoYoneda C) _o) ((×ᶠⁿᶜ C) _o (0, a)))%object)%nattrans
    :=
      {|
        Trans := fun c g => compose C (Pi_1 (CCC_HP C init a)) (t_morph init c)
      |}.
  
  Next Obligation.
  Proof.
    extensionality g.
    simpl_ids.
    rewrite <- assoc.
    apply f_equal.
    apply (t_morph_unique init).
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Init_Prod_rl_obligation_1.
  Qed.

  Theorem Init_Prod a :
    (((×ᶠⁿᶜ C) _o (0, a)%object) ≃ 0)%isomorphism.
  Proof.
    apply (@CoIso (C^op)).
    CoYoneda.
    apply (NatIso _ _ (Init_Prod_lr a) (Init_Prod_rl a)).
    {
      intros c.
      extensionality g; simpl.
      apply (t_morph_unique init).
    }
    {
      intros c.
      eapply functional_extensionality; intros g; simpl; simpl_ids.
      match goal with
          [|- ?A = ?B] =>
          erewrite <- uncurry_curry with(f := A);
            erewrite <- uncurry_curry with (f := B)
      end.
      apply f_equal.
      apply (t_morph_unique init).
    }
  Qed.

End Init_Prod.
