From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Cat.Cat.
From Categories Require Import Basic_Cons.Terminal.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import NatTrans.NatTrans NatTrans.NatIso.

(** The unique functor to the terminal category. *)
Program Definition Functor_To_1_Cat (C' : Category) : (C' –≻ 1)%functor :=
{|
  FO := fun x => tt;
  FA := fun a b f => tt;
  F_id := fun _ => eq_refl;
  F_compose := fun _ _ _ _ _ => eq_refl
|}.

(** Terminal category. *)
Program Instance Cat_Term : (𝟙_ Cat)%object :=
{
  terminal := 1%category;

  t_morph := fun x => Functor_To_1_Cat x
}.

Next Obligation. (* t_morph_unique *)
Proof.
  Func_eq_simpl;
  FunExt;
  match goal with
    [|- ?A = ?B] =>
    destruct A;
      destruct B end;
  trivial.
Qed.  

(** A functor from terminal category maps all arrows (any arrow is just the
    identity) to the identity arrow. *)
Section From_Term_Cat.
  Context {C : Category} (F : (1 –≻ C)%functor).

  Theorem From_Term_Cat : ∀ h, (F @_a tt tt h)%morphism = id.
  Proof.
    destruct h.
    change tt with (id 1 tt).
    apply F_id.
  Qed.

End From_Term_Cat.

(** Any two functors from a category to the terminal categoy are naturally
    isomorphic. *)
Program Definition Functor_To_1_Cat_Iso
        {C : Category}
        (F F' : (C –≻ 1)%functor)
  : (F ≃ F')%natiso :=
{|
  iso_morphism :=
    {|
      Trans := fun _ => tt
    |};
  inverse_morphism :=
    {|
      Trans := fun _ => tt
    |}
|}.
