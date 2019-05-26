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

Section PSh_GenSum.
  Context (C : Category) (A : Type) (map : A → PShCat C).

  Local Notation Fm := (Discr_Func_op (PShCat C) map) (only parsing).

  Local Hint Extern 1 => match goal with [h : {x : _ & _} |- _] => destruct x end.
  Local Hint Extern 1 => match goal with
                          [|- context [(?F _a id)%morphism]] => rewrite (F_id F)
                        end.
  Local Hint Extern 1 =>
  match goal with
    [|- context [(?F _a (?f ∘ ?g))%morphism]] =>
    cbn_rewrite (F_compose F f g)
  end.

  (** The pointwise generalized sum presheaf. *)
  Program Definition PSh_GenSum_func : PreSheaf C :=
    {|
      FO :=
        fun c =>
          {x : A & ((Fm _o x) _o c)%object};
      FA :=
        fun _ _ h x => existT _ (projT1 x)
                           ((map (projT1 x) _a h (projT2 x))%morphism)
    |}.
    
  (** The injection of generalized sum presheaf. *)
  Program Definition PSh_GenProd_inj (x : A) :
    (map x –≻ PSh_GenSum_func)%nattrans :=
    {|
      Trans := fun c y => existT _ x y
    |}.
    
  (** The cone for generalized sum presheaf. *)
  Program Definition PSh_GenSum_CoCone : CoCone Fm :=
    {|
      cone_apex :=
        {|FO := fun _ => PSh_GenSum_func;
          FA :=
            fun _ _ h => id
        |};
      cone_edge := {|Trans := fun x => PSh_GenProd_inj x |}
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
  Program Definition PSh_GenSum_morph_ex
          (Cn : LoKan_Cone
                  (Functor_To_1_Cat (Discr_Cat A ^op) ^op)
                  (Discr_Func_op ((PShCat C))  map ^op)
          )
    : (PSh_GenSum_func –≻ (Cn _o)%object tt)%nattrans :=
    {|
      Trans := fun c y => Trans (Trans Cn (projT1 y)) c (projT2 y)
    |}.
    
  Local Hint Extern 1 => progress cbn.

  Local Obligation Tactic := basic_simpl; auto 10.

  Program Definition PSh_GenSum : (Σ map)%object :=
    {|
      LRKE := PSh_GenSum_CoCone;
      LRKE_morph_ex :=
        fun Cn =>
          {|
            cone_morph :=
              {|
                Trans :=
                  fun x => _
                          match x as u return
                                (PSh_GenSum_func –≻ (Cn _o)%object u)%nattrans
                          with
                            tt => PSh_GenSum_morph_ex Cn
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
    destruct z as [z u].
    cbn in *.
    destruct x.
    cbn_rewrite
      <-
      (
        equal_f
          (
            f_equal
              (fun w :
                     (
                       (Cn ∘ Functor_To_1_Cat (Discr_Cat A ^op) ^op)
                          –≻ Discr_Func_op (PShCat C) map ^op
                     )%nattrans
               =>
                 Trans (Trans w z) y
              ) (cone_morph_com h)
          )
          u
      ).
    cbn_rewrite
      <-
      (
        equal_f
          (
            f_equal
              (fun w :
                     (
                       (Cn ∘ Functor_To_1_Cat (Discr_Cat A ^op) ^op)
                          –≻ Discr_Func_op (PShCat C) map ^op
                     )%nattrans
               =>
                 Trans (Trans w z) y
              ) (cone_morph_com h')
          )
          u
      ).
    trivial.
  Qed.
  
End PSh_GenSum.



(** In category of types, generalized sums are simply dependent sum types. *)
Section Type_Cat_GenSum.
  Context (A : Type) (map : A → Type_Cat).

  Local Notation Fm := (Discr_Func_op Type_Cat map) (only parsing).

  (** The cocone for the colimit of generalized sum. *)
  Program Definition Type_Cat_GenSum_CoCone : CoCone Fm :=
    {|
      cone_apex :=
        {|FO := fun _ => {x : A & (Fm _o x)%object}; FA := fun _ _ _ h => h|};
      cone_edge := {|Trans := fun x => existT _ x |}
    |}.
    
   Program Definition Type_Cat_GenSum : (Σ map)%object :=
    {|
      LRKE := Type_Cat_GenSum_CoCone;
      LRKE_morph_ex :=
        fun Cn =>
          {|
            cone_morph :=
              {|Trans :=
                  fun c h =>
                    match c as u return ((Cn _o) u)%object with
                    | tt => Trans Cn (projT1 h) (projT2 h)
                    end
              |}
          |}
    |}.
   
  Next Obligation.
  Proof.
    extensionality x.
    destruct c; destruct c'; destruct h.
    apply (equal_f (@Trans_com _ _ _ _ Cn (projT1 x) (projT1 x) eq_refl)).
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Type_Cat_GenSum_obligation_1.
  Qed.    

  Next Obligation.
  Proof.
    apply NatTrans_eq_simplify.
    extensionality x; extensionality y.
    destruct x.
    destruct y as [y1 y2].
    cbn in *.
    set (hc := (cone_morph_com h')).
    rewrite (cone_morph_com h) in hc.
    set (hc' := (
                 f_equal
                   (fun w :
                        ((Cn ∘ (Functor_To_1_Cat
                                  (Discr_Cat A)^op) ^op) –≻ Fm^op)%nattrans
                    =>
                      Trans w y1 y2) hc
               )
        ); clearbody hc'; clear hc.
    cbn in *.
    apply hc'.
  Qed.

End Type_Cat_GenSum.
