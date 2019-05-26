From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Cat.Cat.

(* Product Category *)

(** The product of two categories has as objects pairs of objects (first
component from the first category and the second component from the second
category) and as arrows pairs of arrows.
 *)

Local Open Scope morphism_scope.

Local Obligation Tactic := idtac.

Program Definition Prod_Cat (C C' : Category) : Category :=
{|
  Obj := C * C';
              
  Hom :=
    fun a b =>
      (((fst a) –≻ (fst b)) * ((snd a) –≻ (snd b)))%type;

  compose :=
    fun a b c f g =>
      (((fst g) ∘ (fst f)), ((snd g) ∘ (snd f)))%morphism;

  id := fun c => (id, id)
|}.

Next Obligation.
  cbn.
  intros.
  rewrite (assoc (fst _)).
  rewrite assoc.
  trivial.
Defined.

Next Obligation.
  cbn.
  intros C C' a b c d f g h.
  rewrite (assoc_sym (fst _)).
  rewrite assoc_sym.
  trivial.
Defined.

Next Obligation.
  cbn.
  intros.
  rewrite (id_unit_left (fst _)).
  rewrite id_unit_left.
  trivial.
Defined.

Next Obligation.
  cbn.
  intros.
  rewrite (id_unit_right (fst _)).
  rewrite id_unit_right.
  trivial.
Defined.

Notation "C × D" := (Prod_Cat C D) : category_scope.

Local Obligation Tactic := basic_simpl; auto.

Theorem Prod_compose_id
        (C D : Category)
        (a b c : C) (d : D)
        (f : a –≻ b) (g : b –≻ c)
  : (g ∘ f, id d)%morphism =
    @compose (_ × _) (_, _) (_, _) (_, _) (f, id d) (g, id d).
Proof.
  cbn; auto.
Qed.

Theorem Prod_id_compose
        (C D : Category)
        (a : C) (b c d : D)
        (f : b –≻ c) (g : c –≻ d)
  : (id a, g ∘ f)%morphism =
    @compose (_ × _) (_, _) (_, _) (_, _) (id a, f) (id a, g).
Proof.
  cbn; auto.
Qed.

Theorem Prod_cross_compose
        (C D : Category)
        (a b : C) (c d : D)
        (f : a –≻ b) (g : c –≻ d)
  : @compose
      (_ × _) (_, _) (_, _) (_, _)
      (@id _ a, g) (f, @id _ d)
    = @compose
        (_ × _) (_, _) (_, _) (_, _)
        (f, @id _ c) (@id _ b, g)
.
Proof.
  cbn; auto.
Qed.

Program Definition Cat_Proj1
        (C C' : Category) :
  ((C × C') –≻ C)%functor
  :=
    {|FO := fst; FA := fun _ _ f => fst f|}
.

Program Definition Cat_Proj2
        (C C' : Category) :
  ((C × C') –≻ C')%functor
  :=
    {|FO := snd; FA := fun _ _ f => snd f|}
.
