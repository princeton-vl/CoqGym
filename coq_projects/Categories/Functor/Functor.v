From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.

(**
Fro categories C and C', a functor F : C -> C' consists of an arrow map from
objects of C to objects of C' and an arrow map from arrows of C to arrows of C'
such that an arrow h : a -> b is mapped to (F h) : F a -> F b.

Furthermore, we require functors to map identitiies to identities. Additionally,
the immage of the coposition of two arrows must be the same as composition of
their images.
*)
Record Functor (C C' : Category) : Type :=
{
  (** Object map *)
  FO : C → C';

  (** Arrow map *)
  FA : ∀ {a b}, (a –≻ b)%morphism → ((FO a) –≻ (FO b))%morphism;

  (** Mapping of identities *)
  F_id : ∀ c, FA (id c) = id (FO c);

  (** Functor commuting with composition *)
  F_compose : ∀ {a b c} (f : (a –≻ b)%morphism) (g : (b –≻ c)%morphism),
      (FA (g ∘ f) = (FA g) ∘ (FA f))%morphism

  (* F_id and F_compose together state the fact that functors are morphisms of
 categories (preserving the structure of categories!)*)
}.

Arguments FO {_ _} _ _.
Arguments FA {_ _} _ {_ _} _, {_ _} _ _ _ _.
Arguments F_id {_ _} _ _.
Arguments F_compose {_ _} _ {_ _ _} _ _.

Notation "C –≻ D" := (Functor C D) : functor_scope.

Bind Scope functor_scope with Functor.

Notation "F '_o'" := (FO F) : object_scope.

Notation "F '@_a'" := (@FA _ _ F) : morphism_scope.

Notation "F '_a'" := (FA F) : morphism_scope.

Hint Extern 2 => (apply F_id).

Local Open Scope morphism_scope.
Local Open Scope object_scope.

Ltac Functor_Simplify :=
  progress
    (
      repeat rewrite F_id;
      (
        repeat
          match goal with
          | [|- ?F _a ?A = id (?F _o ?x)] =>
            (rewrite <- F_id; (cbn+idtac))
          | [|- (id (?F _o ?x)) = ?F _a ?A] =>
            (rewrite <- F_id; (cbn+idtac))
          | [|- ?F _a ?A ∘ ?F _a ?B = ?F _a ?C ∘ ?F _a ?D] =>
            (repeat rewrite <- F_compose; (cbn+idtac))
          | [|- ?F _a ?A ∘ ?F _a ?B = ?F _a ?C] =>
            (rewrite <- F_compose; (cbn+idtac))
          | [|- ?F _a ?C = ?F _a ?A ∘ ?F _a ?B] =>
            (rewrite <- F_compose; (cbn+idtac))
          | [|- context [?F _a ?A ∘ ?F _a ?B]] =>
            (rewrite <- F_compose; (cbn+idtac))
          end
      )
    )
.

Hint Extern 2 => Functor_Simplify.

Section Functor_eq_simplification.

  Context {C C' : Category} (F G : (C –≻ C')%functor).

  (** Two functors are equal if their object maps and arrow maps are. *)
  Lemma Functor_eq_simplify (Oeq : F _o = G _o) :
    ((fun x y =>
        match Oeq in _ = V return ((x –≻ y) → ((V x) –≻ (V y)))%morphism with
          eq_refl => F  @_a x y
        end) = G @_a) -> F = G.
  Proof.
    destruct F; destruct G.
    basic_simpl.
    ElimEq.
    PIR.
    trivial.
  Qed.

  (** Extensionality for arrow maps of functors. *)
  Theorem FA_extensionality (Oeq : F _o = G _o) :
    (
      ∀ (a b : Obj)
        (h : (a –≻ b)%morphism),
        (
          fun x y =>
            match Oeq in _ = V return
                  ((x –≻ y) → ((V x) –≻ (V y)))%morphism
            with
              eq_refl => F  @_a x y
            end
        ) _ _ h = G _a h
    )
    →
    (
      fun x y =>
        match Oeq in _ = V return
              ((x –≻ y) → ((V x) –≻ (V y)))%morphism
        with
          eq_refl => F  @_a x y
        end
    ) = G @_a.
  Proof.
    auto.
  Qed.

  (** Fucntor extensionality: two functors are equal of their object maps are
      equal and their arrow maps are extensionally equal. *)
  Lemma Functor_extensionality (Oeq : F _o = G _o) :
    (
      ∀ (a b : Obj) (h : (a –≻ b)%morphism),
        (
          fun x y =>
            match Oeq in _ = V return
                  ((x –≻ y) → ((V x) –≻ (V y)))%morphism
            with
              eq_refl => F  @_a x y
            end
        ) _ _ h = G _a h
    ) → F = G.
  Proof.
    intros H.
    apply (Functor_eq_simplify Oeq); trivial.
    apply FA_extensionality; trivial.
  Qed.

End Functor_eq_simplification.

Hint Extern 2 => Functor_Simplify.

Ltac Func_eq_simpl :=
  match goal with
    [|- ?A = ?B :> Functor _ _] =>
    (apply (Functor_eq_simplify A B (eq_refl : A _o = B _o)%object)) +
    (cut (A _o = B _o)%object; [
       let u := fresh "H" in
       intros H;
         apply (Functor_eq_simplify A B H)
         |
    ])
  end.

Hint Extern 3 => Func_eq_simpl.

Section Functor_eq.
  Context {C C' : Category} (F G : (C –≻ C')%functor).

  Lemma Functor_eq_morph (H : F = G) :
    ∃ (H : ∀ x, F _o x = G _o x),
    ∀ x y (h : (x –≻ y)%morphism),
      match H x in _ = V return (V –≻ _)%morphism with
         eq_refl =>
         match H y in _ = V return (_ –≻ V)%morphism with
           eq_refl => F _a h
         end
       end = G _a h.
  Proof.
    exists (equal_f (f_equal FO H)).
    intros x y h.
    destruct H; trivial.
  Qed.

End Functor_eq.
