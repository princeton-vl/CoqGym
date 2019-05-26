From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Coq_Cats.Type_Cat.Type_Cat.

Section Arrow.
  Local Open Scope morphism_scope.

  (** The type accomodating all arrows of a category C. *)
  Record Arrow (C : Category) :=
    {
      Orig : Obj;
      Targ : Obj;
      Arr : Orig –≻ Targ
    }.

  Arguments Orig {_} _.
  Arguments Targ {_} _.
  Arguments Arr {_} _.

  Coercion Arr : Arrow >-> Hom.

  (** An arrow (in the appropriate category, e.g., comma)
    from arrow f : a -> b to arrow g : c -> d is a pair of arrows h1 : a -> c
    and h2 : b -> d that makes the following diagram commute:
#
<pre>
          f
   a ———————————> b
   |              |
h1 |              | h2
   |              |
   ↓              ↓
   c ———————————> d
          g
</pre>
#
 *)
  Record Arrow_Hom {C : Category} (a b : Arrow C) :=
    {
      Arr_H : (Orig a) –≻ (Orig b);
      Arr_H' : (Targ a) –≻ (Targ b);
      Arr_Hom_com : Arr_H' ∘ (Arr a) = (Arr b) ∘ Arr_H
    }.
  Arguments Arr_H {_ _ _} _.
  Arguments Arr_H' {_ _ _} _.
  Arguments Arr_Hom_com {_ _ _} _.

  Context (C : Category).

  Section Arrow_Hom_eq_simplify.
    Context {a b : Arrow C} (f g : Arrow_Hom a b).

    (** Two arrow homomorphisms are equal if the arrows between theor domains
        and codomain are respectively equal. In other words, we don't care about
        the proof of the diagram commuting. *)
    Lemma Arrow_Hom_eq_simplify : Arr_H f = Arr_H g → Arr_H' f = Arr_H' g → f = g.
    Proof.
      destruct f; destruct g.
      basic_simpl.
      ElimEq.
      PIR.
      reflexivity.
    Qed.

  End Arrow_Hom_eq_simplify.

  Section Compose_id.
    Context {x y z} (h : Arrow_Hom x y) (h' : Arrow_Hom y z).

    (** Composition of arrow homomorphisms. We basicall need to show that in the
        following diagram, the bigger diagram commutes if the smaller ones do.
#
<pre>
           f
    a ———————————> b
    |              |
 h1 |              | h2
    |              |
    ↓              ↓
    c ———————————> d
    |      g       |
h1' |              | h2'
    |              |
    ↓              ↓
    c ———————————> d
           h
</pre>
#
*)
    Program Definition Arrow_Hom_compose : Arrow_Hom x z :=
      {|
        Arr_H := (Arr_H h') ∘ (Arr_H h);
        Arr_H' := (Arr_H' h') ∘ (Arr_H' h)
      |}.

    Next Obligation. (* Arr_Hom_com *)
    Proof.
      destruct h as [hh hh' hc]; destruct h' as [h'h h'h' h'c]; cbn.
      rewrite assoc.
      rewrite hc.
      repeat rewrite assoc_sym.
      rewrite h'c.
      auto.
    Qed.

    (** The identity arrow morphism. We simply need to show that the following
        diagram commutes:
#
<pre>
          f
   a ———————————> b
   |              |
id |              | id
   |              |
   ↓              ↓
   a ———————————> b
          f
</pre>
#
which is trivial.
 *)
    Program Definition Arrow_id : Arrow_Hom x x :=
      {|
        Arr_H := id;
        Arr_H' := id
      |}.

  End Compose_id.

End Arrow.

Hint Extern 1 (?A = ?B :> Arrow_Hom _ _) => apply Arrow_Hom_eq_simplify; simpl.

Arguments Orig {_} _.
Arguments Targ {_} _.
Arguments Arr {_} _.

Arguments Arr_H {_ _ _} _.
Arguments Arr_H' {_ _ _} _.
Arguments Arr_Hom_com {_ _ _} _.

(** an arrow in a category is also an arrow in the opposite category. 
    The domain and codomain are simply swapped. *)
Program Definition Arrow_to_Arrow_OP (C : Category) (ar : Arrow C) :
  Arrow (C ^op) :=
  {|
    Arr := ar
  |}.

(** The type of arrows of a category and the type of arrows of its opposite are
     isomorphic. *)
Program Definition Arrow_OP_Iso (C : Category) :
  ((Arrow C) ≃≃ (Arrow (C ^op)) ::> Type_Cat)%isomorphism :=
  {|
    iso_morphism := Arrow_to_Arrow_OP C;
    inverse_morphism := Arrow_to_Arrow_OP (C ^op)
  |}.
