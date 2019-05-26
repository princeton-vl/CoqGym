From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Basic_Cons.CCC Basic_Cons.PullBack.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import PreSheaf.PreSheaf.

Section PSh_PullBack.
  Context (C : Category) {F G I : PreSheaf C}
          (f : (F –≻ I)%nattrans) (g : (G –≻ I)%nattrans).

  Local Hint Extern 1 =>
  match goal with
    [x : sig _ |- _ ] =>
    let H := fresh "H" in
    destruct x as [x H]
  end.

  Local Hint Extern 1 => match goal with
                          [|- context [(?F _a id)%morphism]] => rewrite (F_id F)
                        end.
  Local Hint Extern 1 =>
  match goal with
    [|- context [(?F _a (?f ∘ ?g))%morphism]] =>
    cbn_rewrite (F_compose F f g)
  end.

  Local Hint Extern 1 =>
  match goal with
    [|- context [Trans ?f _ ((?F _a)%morphism ?h _)]] =>
    cbn_rewrite (equal_f (Trans_com f h))
  end.

  Local Hint Extern 1 => progress cbn in *.

  Local Obligation Tactic := basic_simpl; auto 10.

  (** The pointwise pullback presheaf. *)
  Program Definition PSh_PullBack_Func : PreSheaf C :=
    {|
      FO :=
        fun c =>
          {x : ((F _o c) * (G _o c))%object%type |
           Trans f c (fst x) = Trans g c (snd x)
          };
      FA :=
        fun c c' h x =>
          exist
            _
            ((F _a h (fst (proj1_sig x)))%morphism,
             (G _a h (snd (proj1_sig x)))%morphism)
            _
    |}.

  (** The morphism from the pullback to the domain object of the first
      morphism. *)
  Program Definition PSh_PullBack_morph_1 : (PSh_PullBack_Func –≻ F)%nattrans :=
    {|
      Trans := fun c x => fst (proj1_sig x)
    |}.

  (** The morphism from the pullback to the domain object of the second
      morphism. *)
  Program Definition PSh_PullBack_morph_2 : (PSh_PullBack_Func –≻ G)%nattrans :=
    {|
      Trans := fun c x => snd (proj1_sig x)
    |}.

  (** The morphism from the candidate pullback to the pullback. *)
  Program Definition PSh_PullBack_morph_ex
          (p' : (C ^op –≻ Type_Cat)%functor)
          (pm1 : (p' –≻ F)%nattrans)
          (pm2 : (p' –≻ G)%nattrans)
          (H : (f ∘ pm1)%nattrans = (g ∘ pm2)%nattrans)
    :
      (p' –≻ PSh_PullBack_Func)%nattrans
    :=
      {|
        Trans :=
          fun c x =>
            exist
              _
              (Trans pm1 c x, Trans pm2 c x)
              (f_equal (fun w : (p' –≻ I)%nattrans => Trans w c x) H)
      |}.

  (** The pointwise pullback presheaf is the pullback of presheaves. *)
  Program Definition PSh_PullBack : @PullBack (PShCat C) _ _ _ f g :=
    {|
      pullback := PSh_PullBack_Func;
      pullback_morph_1 := PSh_PullBack_morph_1;
      pullback_morph_2 := PSh_PullBack_morph_2;
      pullback_morph_ex := PSh_PullBack_morph_ex
    |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros p' pm1 pm2 H u u' H1 H2 H3 H4.
    rewrite <- H3 in H1; clear H3.
    rewrite <- H4 in H2; clear H4.
    apply NatTrans_eq_simplify.
    extensionality c.
    extensionality x.
    assert (H1' := f_equal (fun w : (p' –≻ F)%nattrans => Trans w c x) H1);
      clear H1.
    assert (H2' := f_equal (fun w : (p' –≻ G)%nattrans => Trans w c x) H2);
      clear H2.
    cbn in *.
    match goal with
      [|- ?A = ?B] => destruct A as [[? ?] ?]; destruct B as [[? ?] ?]
    end.
    apply sig_proof_irrelevance.
    cbn in *; subst; trivial.
  Qed.    

End PSh_PullBack.

Instance PSh_Has_PullBacks (C : Category) : Has_PullBacks (PShCat C) :=
  @PSh_PullBack C.
