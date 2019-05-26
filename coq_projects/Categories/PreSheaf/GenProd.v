From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Limits.Limit Limits.GenProd_GenSum.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import PreSheaf.PreSheaf.
From Categories Require Import NatTrans.NatTrans NatTrans.Func_Cat.

Section PSh_GenProd.
  Context (C : Category) (A : Type) (map : A → PShCat C).

  Local Notation Fm := (Discr_Func (PShCat C) map) (only parsing).

  Local Hint Extern 1 => match goal with
                          [|- context [(?F _a id)%morphism]] => rewrite (F_id F)
                        end.
  Local Hint Extern 1 =>
  match goal with
    [|- context [(?F _a (?f ∘ ?g))%morphism]] =>
    cbn_rewrite (F_compose F f g)
  end.

  (** The generalized product presheaf. *)
  Program Definition PSh_GenProd_func : PreSheaf C :=
    {|
      FO :=
        fun c =>
          ∀ x : A, ((Fm _o x) _o c)%object;
      FA :=
        fun _ _ h f x => (map x _a h (f x))%morphism
    |}.

  (** The projections of generalized product presheaf. *)
  Program Definition PSh_GenProd_proj (x : A) :
    (PSh_GenProd_func –≻ map x)%nattrans :=
    {|
      Trans := fun c y => y x
    |}.

  (** The cone for generalized product presheaf. *)
  Program Definition PSh_GenProd_Cone : Cone Fm :=
    {|
      cone_apex :=
        {|FO := fun _ => PSh_GenProd_func;
          FA :=
            fun _ _ h => id
        |};
      cone_edge := {|Trans := fun x => PSh_GenProd_proj x |}
    |}.

  Local Hint Extern 1 =>
    match goal with
      [|- context [Trans ?f _ ((?F _a)%morphism ?h _)]] =>
      cbn_rewrite (equal_f (Trans_com f h))
    end.

  Local Hint Extern 1 => match goal with [H : unit |- _] => destruct H end.

  Local Hint Resolve NatTrans_eq_simplify.

  Local Hint Extern 1 => rewrite From_Term_Cat.
  
  (** The morphism that maps to the generalized product given a map to its
      components. *)
  Program Definition PSh_GenProd_morph_ex
          (Cn : LoKan_Cone (Functor_To_1_Cat
                              (Discr_Cat A)) (Discr_Func (PShCat C) map))
    : ((Cn _o)%object tt –≻ PSh_GenProd_func)%nattrans :=
    {|
      Trans := fun c y x => Trans (Trans (cone_edge Cn) x) c y
    |}.

  Local Hint Extern 1 => progress cbn.

  Local Obligation Tactic := basic_simpl; auto 10.

  Program Definition PSh_GenProd : (Π map)%object :=
    {|
      LRKE := PSh_GenProd_Cone;
      LRKE_morph_ex :=
        fun Cn =>
          {|
            cone_morph :=
              {|
                Trans :=
                  fun x =>
                    match x as u return
                          ((Cn _o)%object u –≻ PSh_GenProd_func)%nattrans
                    with
                      tt => PSh_GenProd_morph_ex Cn
                    end
              |}
          |}
    |}.

  Local Obligation Tactic := idtac.

  Next Obligation.
  Proof.
    intros Cn h h'.
    apply NatTrans_eq_simplify.
    extensionality x.
    apply NatTrans_eq_simplify.
    extensionality y.
    extensionality z.
    extensionality u.
    cbn in *.
    destruct x.
    cbn_rewrite
      <-
      (
        equal_f
          (
            f_equal
              (
                fun w : (Cn ∘ Functor_To_1_Cat
                          (Discr_Cat A) –≻ Discr_Func (PShCat C) map)%nattrans
                => Trans (Trans w u) y
              )
              (cone_morph_com h)
          )
          z
      ).
    cbn_rewrite
      <-
      (
        equal_f
          (
            f_equal
              (
                fun w : (Cn ∘ Functor_To_1_Cat
                          (Discr_Cat A) –≻ Discr_Func (PShCat C) map)%nattrans
                => Trans (Trans w u) y
              )
              (cone_morph_com h')
          )
          z
      ).
    trivial.
  Qed. 

End PSh_GenProd.
