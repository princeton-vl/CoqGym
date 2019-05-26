From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.
From Categories Require Import Basic_Cons.Product.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import PreSheaf.PreSheaf.

Section Sum.
  Context (C : Category) (F G : PShCat C).

  Local Hint Extern 1 => match goal with
                          [H : (_ + _)%type |- _] => destruct H
                        end.
  Local Hint Extern 1 => match goal with
                          [|- context [(?F _a id)%morphism]] => rewrite (F_id F)
                        end.
  Local Hint Extern 1 =>
  match goal with
    [|- context [(?F _a (?f ∘ ?g))%morphism]] =>
    cbn_rewrite (F_compose F f g)
  end.
  
  (** The pointwise sum of presheaves F and G. *)
  Program Definition PSh_Sum_Func : PShCat C :=
    {|
      FO := fun c => ((F _o c) + (G _o c))%type%object;
      FA :=
        fun c d h x =>
          match x return ((F _o d) + (G _o d))%type%object with
          | inl xl => inl (F _a h xl)%morphism
          | inr xr => inr (G _a h xr)%morphism
          end
    |}.

  (** Pointwise left injection. *)
  Program Definition PSh_Sum_injl : NatTrans F PSh_Sum_Func :=
    {|
      Trans := fun c x => inl x
    |}.

  (** Pointwise right injection. *)
  Program Definition PSh_Sum_injr : NatTrans G PSh_Sum_Func :=
    {|
      Trans := fun c x => inr x
    |}.

  Local Hint Extern 1 =>
  match goal with
    [|- context [Trans ?f _ ((?F _a)%morphism ?h _)]] =>
    cbn_rewrite (equal_f (Trans_com f h))
  end.

  (** Pointwise morphism into sum constructed out of two morphisms
from summands. *)
  Program Definition PSh_Sum_morph_ex
          (H : PreSheaf C)
          (f : NatTrans F H)
          (g : NatTrans G H):
    NatTrans PSh_Sum_Func H :=
    {|
      Trans :=
        fun c x =>
          match x return (H _o c)%object with
          | inl xl => Trans f c xl
          | inr xr => Trans g c xr
          end
    |}.
  
  Local Notation "F + G" := (Sum (PShCat C) F G) : object_scope.
  
  (** The pointwise sum presheaf is the sum of presheaves. *)
  Program Definition PSh_Sum : (F + G)%object :=
    {|
      product  := PSh_Sum_Func;
      Pi_1 := PSh_Sum_injl;
      Pi_2 := PSh_Sum_injr;
      Prod_morph_ex := PSh_Sum_morph_ex
    |}.

  Local Obligation Tactic := idtac.
  
  Next Obligation.
  Proof.
    intros p' r1 r2 f g H1 H2 H3 H4.
    rewrite <- H3 in H1; rewrite <- H4 in H2;
    clear H3 H4.
    apply NatTrans_eq_simplify.
    extensionality c; extensionality x.
    destruct x as [x1|x2].
    + apply (f_equal (fun w : (F –≻ p')%nattrans => Trans w c x1) H1).
    + apply (f_equal (fun w : (G –≻ p')%nattrans => Trans w c x2) H2).
  Qed.
  
End Sum.

Instance PSh_Has_Sums (C : Category) : Has_Sums (PShCat C) := PSh_Sum C.
