From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Ext_Cons.Prod_Cat.Prod_Cat.
From Categories Require Import Functor.Main.
From Categories Require Import Basic_Cons.Product.

Local Open Scope morphism_scope.

(**
Given two objects a and b the exponential (bᵃ, denoted 'Exponential a b' below)
is intuitively the internal representation of homomorphisms from a to b – it is
sometimes referred to as the internal hom. The notion of exponential is a
generalization of the notion function space from set theory.

Definition: bᵃ is an object equipped with an evaluation function eval: bᵃ×a -> b
such that for any other object z with arrow f : z×a -> b, we have a unique arrow
f^ that makes the following diagram commute:

#
<pre>
               eval
        bᵃ×a ——————————> b
         ↑             ↗
  bᵃ     |            /
  ↑      | <f^,idₐ>  /
  |      |          /
  |∃!f̂ ^  |         /
  |      |        / f
  z      |       /
         |      /
         |     /
         |    /
         |   /
         |  /
         z×a
</pre>
#
where <f, g> is the arrow map of the product functor.
*)
Record Exponential {C : Category} {HP : Has_Products C} (c d : Obj) : Type :=
{
  exponential : C;

  eval : ((×ᶠⁿᶜ C) _o (exponential, c))%object –≻ d;

  Exp_morph_ex : ∀ (z : C), (((×ᶠⁿᶜ C) _o (z, c))%object –≻ d) → (z –≻ exponential);

  Exp_morph_com : ∀ (z : C) (f : ((×ᶠⁿᶜ C) _o (z, c))%object –≻ d),
      f = (eval ∘ ((×ᶠⁿᶜ C) @_a (_, _) (_, _) (Exp_morph_ex z f, id c)))%morphism;

  Exp_morph_unique : ∀ (z : C) (f : ((×ᶠⁿᶜ C) _o (z, c))%object –≻ d)
                       (u u' : z –≻ exponential),
      f = (eval ∘ ((×ᶠⁿᶜ C) @_a (_, _) (_, _) (u, id c)))%morphism →
      f = (eval ∘ ((×ᶠⁿᶜ C) @_a (_, _) (_, _) (u', id c)))%morphism →
      u = u'
}.

Coercion exponential : Exponential >-> Obj.

Arguments Exponential _ {_} _ _, {_ _} _ _.

Arguments exponential {_ _ _ _} _, {_ _} _ _ {_}.
Arguments eval {_ _ _ _} _, {_ _} _ _ {_}.
Arguments Exp_morph_ex {_ _ _ _} _ _ _, {_ _} _ _ {_} _ _.
Arguments Exp_morph_com {_ _ _ _} _ _ _, {_ _} _ _ {_} _ _.
Arguments Exp_morph_unique {_ _ _ _} _ _ _ _ _ _ _, {_ _} _ _ {_} _ _ _ _ _ _.

Notation "a ⇑ b" := (Exponential a b) : object_scope.

(** Exponentials are unique up to isomorphism. *)
Theorem Exponential_iso {C : Category} {HP : Has_Products C} (c d : C)
        (E E' : (c ⇑ d)%object) : (E ≃ E')%isomorphism.
Proof.
  eapply
    (
      Build_Isomorphism
        _
        _
        _
        (Exp_morph_ex E' _ (eval E))
        (Exp_morph_ex E _ (eval E'))
    );
  eapply Exp_morph_unique; eauto;
  simpl_ids;
  match goal with
      [|- (_ ∘ ?M)%morphism = _] =>
      match M with
        (?U _a (?A ∘ ?B, ?C))%morphism =>
        assert (M = (U @_a (_, _) (_, _) (A, C))
                          ∘ (U @_a (_, _) (_, _) (B, C)))%morphism as HM;
          [simpl_ids; rewrite <- F_compose; simpl; simpl_ids; trivial|rewrite HM]
      end
  end;
  rewrite <- assoc;
  repeat rewrite <- Exp_morph_com; auto.
Qed.

Definition Has_Exponentials (C : Category) {HP : Has_Products C} :=
  ∀ a b, (a ⇑ b)%object.

Existing Class Has_Exponentials.

Section Curry_UnCurry.
  Context (C : Category) {HP : Has_Products C} {HE : Has_Exponentials C}.

  (** Given a arrow f: a×b -> c in a category with exponentials, the curry of f
      is f̂f^ in the definition of Exponential above. *)
  Definition curry :
    forall {a b c : C},
      (((×ᶠⁿᶜ C) _o (a, b))%object –≻ c) → (a –≻ (HE b c)) :=
    fun {a b c : C} (f : ((×ᶠⁿᶜ C) _o (a, b))%object –≻ c) =>
      Exp_morph_ex (HE b c) _ f.

  (** Given an arrow f: a -> cᵇ, uncurry of f is the arrow
      (eval_cᵇ ∘ <id_b, f>): a×b -> c.
      See definition of Exponential above for details. *)
  Definition uncurry : forall {a b c : C},
      (a –≻ (HE b c)) → (((×ᶠⁿᶜ C) _o (a, b))%object –≻ c) :=
    fun {a b c : C} (f : a –≻ (HE b c)) =>
      ((eval (HE b c)) ∘ ((×ᶠⁿᶜ C) @_a (_, _) (_, _) (f, id C b)))%morphism.

  Section inversion.
    Context {a b c : C}.

    (** See definition of curry and uncurry above for details.
        Frollows immediately from the definition of Exponential above. *)
    Theorem curry_uncurry (f : a –≻ (HE b c)) : curry (uncurry f) = f.
    Proof.
      unfold curry, uncurry.
      eapply Exp_morph_unique; trivial.
      rewrite <- Exp_morph_com; trivial.
    Qed.

    (** See definition of curry and uncurry above for details.
        Follows immediately from the definition of Exponential above. *)
    Theorem uncurry_curry (f : ((×ᶠⁿᶜ C) _o (a, b))%object –≻ c) :
      uncurry (curry f) = f.
    Proof.
      unfold curry, uncurry.
      rewrite <- Exp_morph_com; trivial.
    Qed.

  End inversion.

  Section injectivity.
    Context {a b c : C}.

    (** See definition of curry above for details. Follows immediately from
        uncurry_curry above. *)
    Theorem curry_injective (f g : ((×ᶠⁿᶜ C) _o (a, b))%object –≻ c) :
      curry f = curry g → f = g.
    Proof.
      intros H.
      rewrite <- (uncurry_curry f); rewrite <- (uncurry_curry g).
      rewrite H; trivial.
    Qed.

    (** See definition of uncurry above for details.
        Follows immediately from curry_uncurry above. *)
    Theorem uncurry_injective (f g : a –≻ (HE b c)) :
      uncurry f = uncurry g → f = g.
    Proof.
      intros H.
      rewrite <- (curry_uncurry f); rewrite <- (curry_uncurry g).
      rewrite H; trivial.
    Qed.

  End injectivity.

  Section curry_compose.
    Context {a b c : C}.

    (** composing with curry is equivalent to compose and then curry: *)
    Lemma curry_compose (f : ((×ᶠⁿᶜ C) _o (a, b))%object –≻ c)
          {z : C} (g : z –≻ a)
      : (curry f) ∘ g = curry (f ∘ (Prod_morph_ex _ _ (g ∘ Pi_1) Pi_2)).
    Proof.
      unfold curry.
      eapply Exp_morph_unique; eauto.
      rewrite <- Exp_morph_com.
      match goal with
          [|- ((_ ∘ (_ _a) ?M) ∘ _)%morphism = _] =>
          match M with
              ((?N ∘ ?x)%morphism, id ?y) =>
              replace M with
              (compose (_ × _) (_, _) (_, _) (_, _) (x, id y) (N,id y)) by
                  (cbn; auto)
          end
      end.
      rewrite F_compose.
      cbn; simpl_ids.
      rewrite assoc_sym.
      match goal with
          [|- (?A ∘ ?B = ?C ∘ ?B)%morphism] => cutrewrite (A = C); trivial
      end.
      transitivity (uncurry (curry f));
        [unfold curry, uncurry; cbn; auto|apply uncurry_curry].
    Qed.

  End curry_compose.

End Curry_UnCurry.
