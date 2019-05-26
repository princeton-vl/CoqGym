From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Basic_Cons.CCC Basic_Cons.LCCC Basic_Cons.PullBack.
From Categories Require Import Ext_Cons.Comma.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.PullBack.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Functor.Functor_Ops Functor.Const_Func.

(** Type_Cat is locally cartesian closed. *)
Section CCC_Slice_A.
  Context {A : Type}.

  (** Notation for creating objects of slice out of arrows to A. *)
  Local Notation CO z :=
    (
      @Build_Comma_Obj
        Type_Cat
        Type_Cat
        1
        (Functor_id Type_Cat)
        (@Const_Func 1 Type_Cat A)
        _
        tt
        z
    ) (only parsing).

  (** The slice has products because Type_Cat has pullbacks. *)
  Definition Type_Cat_Slice_Prod :
    Has_Products (Slice Type_Cat A) :=
    @Has_PullBack_Slice_Has_Prod Type_Cat Type_Cat_Has_PullBacks A
  .

  (** Here we show that slices have exponentials. *)

  (** 
Given two arrows f : Y → A and g : Y → A, the exponential gᶠ is an arrow
from {(z, u)| z : A, u : (f⁻¹ z) → (g⁻¹ z)} to A that maps a pair
(z, u) to z.
      
Intuitively, exponentials are representatives of the set of morphisms between
objects. Recall that in a slice, a morphism from f : X → A to g : Y → A is a
morphism h : X → Y that makes the following diagram commute.

         h
    X ——————–> Y
    |         /
    |       /
  f |     / g
    |   /
    ↓ ↙
    A

Therefore, for any element z : A, arrows from (f⁻¹ z) to (g⁻¹ z) are precisely
those that make the diagram commute.
*)

  Context (f g : Slice Type_Cat A).

  Definition Pre_Image {X : Type} (f : X → A) (z : A) := {y : X| f y = z}.

  Local Notation EXP :=
    (
      CO
        (
          fun m : {x : A & (Pre_Image (CMO_hom f) x) → (Pre_Image (CMO_hom g) x)}
          => projT1 m
        )
    ) (only parsing).

  Local Obligation Tactic := idtac.

  Program Definition Type_Cat_LExp :
    @Exponential (Slice Type_Cat A) Type_Cat_Slice_Prod f g :=
    {|
      exponential := EXP;
      eval :=
        @Build_Comma_Hom
          Type_Cat
          Type_Cat
          1
          (Functor_id Type_Cat)
          (@Const_Func 1 Type_Cat A)
          _
          _
          (fun w =>
             proj1_sig
               ((projT2 (fst (proj1_sig w))) (exist _ (snd (proj1_sig w)) _)))
          tt
          _
      ;
      Exp_morph_ex :=
        fun z h =>
          @Build_Comma_Hom
            Type_Cat
            Type_Cat
            1
            (Functor_id Type_Cat)
            (@Const_Func 1 Type_Cat A)
            z
            EXP
            (fun w =>
               existT
                 _
                 (CMO_hom z w)
                 (fun v => exist _ (CMH_left h (exist _ (w, proj1_sig v) _)) _)
            )
            tt
            _
    |}.

  Next Obligation.
  Proof.
    intros w.
    exact (eq_sym (proj2_sig w)).
  Qed.

  Next Obligation.
  Proof.
    extensionality w.
    destruct w as [[[x h] z] H]; cbn in *.
    match goal with
      [|- _ = CMO_hom g (proj1_sig ?A)] =>
      destruct A as [a H1]; cbn; auto
    end.
  Qed.

  Next Obligation.
  Proof.
    intros z h w v.
    symmetry.
    apply (proj2_sig v).
  Qed.

  Next Obligation.
  Proof.
    intros z h w v.
    symmetry.
    exact (equal_f
             (CMH_com h)
             (exist _ (w, proj1_sig v) (Type_Cat_LExp_obligation_3 z h w v))).
  Qed.

  Next Obligation.
  Proof.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    intros z h; simpl.
    apply Comma_Hom_eq_simplify;
      [
        extensionality x |
        match goal with
          [|- ?A = ?B] =>
          destruct A; destruct B; trivial
        end
      ].
    cbn in *.
    apply f_equal.
    destruct x as [x H].
    apply sig_proof_irrelevance; trivial.
  Qed.

  Next Obligation.
  Proof.
    intros z h u u' H1 H2; simpl.
    rewrite H1 in H2; clear H1.
    apply Comma_Hom_eq_simplify;
      [extensionality x|
       match goal with
         [|- ?A = ?B] =>
         destruct A; destruct B; trivial
       end
      ].
    set (Hp1 :=
           equal_f
             (eq_trans (eq_sym (CMH_com u)) (CMH_com u'))
             x
        ); clearbody Hp1; cbn in Hp1.
    match goal with
      [|- ?A = ?B] =>
      cut (match Hp1 in _ = y return
                 Pre_Image (CMO_hom f) y → Pre_Image (CMO_hom g) y
           with
             eq_refl => projT2 A
           end = projT2 B
          );
        [intros Hp2; destruct A as [za Fa]; destruct B as [zb Fb]|]
    end.
    {
      cbn in Hp1, Hp2.
      destruct Hp1; destruct Hp2; trivial.
    }
    {
      extensionality v.
      transitivity
        (match Hp1 in _ = y return
               Pre_Image (CMO_hom g) y
         with
           eq_refl =>
           projT2
             (CMH_left u x)
             (match eq_sym Hp1 in _ = y return
                    Pre_Image (CMO_hom f) y
              with
                eq_refl => v
              end)
         end
        ).
      {
        destruct Hp1; trivial.
      }
      set (M :=
             exist
               (fun w => CMO_hom z (fst w) = CMO_hom f (snd w))
               (x, proj1_sig v)
               (eq_trans
                  (equal_f (CMH_com u') x)
                  (eq_sym (proj2_sig v))
               )
          ).
      set (H2' := (equal_f (f_equal CMH_left H2) M));clearbody H2'; clear H2.
      cbn in H2'.
      match type of H2' with
        proj1_sig (projT2 (CMH_left u x) ?w) =
        proj1_sig (projT2 (CMH_left u' x) ?w') =>
        cutrewrite
          (w =
           (
             match eq_sym Hp1 in _ = y return
                   Pre_Image (CMO_hom f) y
             with
               eq_refl => v
             end
           )
          ) in H2'; [cutrewrite (w' = v) in H2' |]
      end.
      {
        apply sig_proof_irrelevance.
        etransitivity; [|apply H2'].
        generalize (
            (
              match eq_sym Hp1 in (_ = y) return
                    (Pre_Image (CMO_hom f) y)
              with
                eq_refl => v
              end
            )
          ) as p.
        intros p.
        clear.
        destruct Hp1.
        trivial.
      }
      {
        clear.
        apply sig_proof_irrelevance; trivial.
      }
      {
        clear.
        apply sig_proof_irrelevance; cbn.
        destruct (eq_sym Hp1); trivial.
      }
    }
  Qed.

End CCC_Slice_A.

(** Type_Cat is locally cartesian closed. *)
Instance Type_Cat_LCCC : LCCC Type_Cat :=
  fun A =>
    {|
      CCC_term := Slice_Terminal Type_Cat A;
      CCC_HP := Type_Cat_Slice_Prod;
      CCC_HEXP := Type_Cat_LExp
    |}.
