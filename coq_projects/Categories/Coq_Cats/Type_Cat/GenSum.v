From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.
From Categories Require Import Limits.Limit Limits.GenProd_GenSum.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Basic_Cons.Terminal.

(** In category of types, generalized sums are simply dependent sum types. *)
Section Type_Cat_GenSum.
  Context (A : Type) (map : A → Type_Cat).

  Local Notation Fm := (Discr_Func_op Type_Cat map) (only parsing).

  (** The cocone for the colimit of generalized sum. *)
  Program Definition Type_Cat_GenSum_CoCone : CoCone Fm :=
    {|
      cone_apex := {|FO := fun _ => {x : A & (Fm _o x)%object};
                     FA := fun _ _ _ h => h|};
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
                        ((Cn ∘ (Functor_To_1_Cat (Discr_Cat A)^op) ^op)
                           –≻ Fm^op)%nattrans
                    =>
                      Trans w y1 y2) hc
               )
        ); clearbody hc'; clear hc.
    cbn in *.
    apply hc'.
  Qed.

End Type_Cat_GenSum.
