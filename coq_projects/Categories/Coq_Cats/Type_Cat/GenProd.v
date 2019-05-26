From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Limits.Limit Limits.GenProd_GenSum.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Basic_Cons.Terminal.

(** In category of types, generalized products are simply dependent prdoducts. *)
Section Type_Cat_GenProd.
  Context (A : Type) (map : A → Type_Cat).

  Local Notation Fm := (Discr_Func Type_Cat map) (only parsing).

  Program Definition Type_Cat_GenProd_Cone : Cone Fm :=
    {|
      cone_apex := {|FO := fun _ => ∀ x : A, (Fm _o x)%object; FA := fun _ _ _ h => h|};
      cone_edge := {|Trans := fun x y => y x |}
    |}.

  Program Definition Type_Cat_GenProd : (Π map)%object :=
    {|
      LRKE := Type_Cat_GenProd_Cone;
      LRKE_morph_ex :=
        fun Cn =>
          {|
            cone_morph :=
              {|Trans :=
                  fun c X x  =>
                    match c as u return ((Cn _o)%object u → map x) with
                    | tt => fun X : (Cn _o)%object tt => Trans Cn x X
                    end X
              |}
          |}
    |}.

  Next Obligation.
  Proof.
    destruct c; destruct c'; destruct h.
    extensionality x; extensionality y.
    apply (equal_f ((@Trans_com _ _ _ _ Cn) y y eq_refl) x).
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Type_Cat_GenProd_obligation_1.
  Qed.

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x; extensionality y; extensionality z.
    destruct x.
    set (hc := (cone_morph_com h')).
    rewrite (cone_morph_com h) in hc.
    set (hc' := (f_equal (fun w :
                  ((Cn ∘ (Functor_To_1_Cat (Discr_Cat A))) –≻ Fm)%nattrans =>
           Trans w z y) hc)); clearbody hc'; clear hc.
    trivial.
  Qed.    

End Type_Cat_GenProd.
