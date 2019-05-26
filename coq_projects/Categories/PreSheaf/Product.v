From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.CCC.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Product.
From Categories Require Import PreSheaf.PreSheaf.

Section Product.
  Context (C : Category) (F G : PShCat C).

  
  Local Hint Extern 1 =>
  match goal with
    [F : (_ ^op –≻ Type_Cat)%functor |- _] => rewrite (F_id F)
  end.
  Local Hint Extern 1 =>
  match goal with
    [F : (_ ^op –≻ Type_Cat)%functor |- context [(F _a (?f ∘ ?g))%morphism]] =>
    cbn_rewrite (F_compose F f g)
  end.

  (** The pointwise product presheaf. *)
  Program Definition pointwise_product_psh : PShCat C :=
    {|
      FO := fun x => ((F _o x) * (G _o x))%object%type;
      FA := fun _ _ f u => (F _a f (fst u), G _a f (snd u))%morphism%object
    |}.
    
  Local Hint Extern 1 =>
  repeat
    match goal with
      [f : (?p –≻ _)%nattrans,
           h : (_ –≻ _)%morphism, c : _, x : (?p _o)%object _ |- _] =>
      cbn_rewrite (equal_f (Trans_com f h) x)
    end.
  
  (** The pointwise product presheaf is the product of presheaves. *)
  Program Definition PSh_Product : (F × G)%object :=
    {|
      product := pointwise_product_psh;
      Pi_1 := {| Trans := fun _ => fst |};
      Pi_2 := {| Trans := fun _ => snd |};
      Prod_morph_ex :=
        fun p' f g => {|Trans := fun x u => (Trans f x u, Trans g x u) |}
    |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros p' r1 r2 f g H1 H2 H3 H4; cbn in *.
    rewrite <- H3 in H1; rewrite <- H4 in H2; clear H3 H4.
    apply NatTrans_eq_simplify.
    extensionality v; extensionality z.
    assert (W1 := f_equal (fun w : (p' –≻ F)%nattrans => Trans w v z) H1).
    assert (W2 := f_equal (fun w : (p' –≻ G)%nattrans => Trans w v z) H2).
    cbn in W1, W2.
    match goal with
      [|- ?A = ?B] => destruct A; destruct B; cbn in *; auto
    end.
  Qed.    

End Product.

Instance PSh_Has_Products (C : Category) : Has_Products (PShCat C) :=
  PSh_Product C.
