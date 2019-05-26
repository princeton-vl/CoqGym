From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Category.
Local Open Scope morphism_scope.

(** A composable chain in a category from a to b is a single arrow from a to b
or an arrow from a to some c provided that there is a composable chain from c
to b.

Composable chains are used in defining images of functors.
*)
Inductive Composable_Chain (C : Category) (a b : C) : Type :=
| Single : (a –≻ b) → Composable_Chain C a b
| Chain : ∀ (c : Obj),
    (a –≻ c) → Composable_Chain C c b → Composable_Chain C a b
.

Arguments Single {_ _ _} _.
Arguments Chain {_ _ _ _} _ _.

(**
A forall quantifier ofr arrows on a composable chain. Forall ch P is provable if
P x is provable for all arrows x on the composable chain ch.
*)
Fixpoint Forall_Links {C : Category} {a b : C} (ch : Composable_Chain C a b)
         (P : ∀ {x y : Obj}, (x –≻ y) → Prop) : Prop :=
  match ch with
    | Single f => P f
    | Chain f ch' => P f ∧ Forall_Links ch' (@P)
  end.

(**
Computes the composition of a composable chain.
*)
Fixpoint Compose_of {C : Category} {a b : C} (ch : Composable_Chain C a b)
         {struct ch} : a –≻ b :=
  match ch with
    | Single f => f
    | Chain f ch' => (Compose_of ch') ∘ f
  end.

(**
Composes two composable chains (chain-composition).
*)
Fixpoint Chain_Compose {C : Category} {a b c : C} (ch1 : Composable_Chain C a b)
         (ch2 : Composable_Chain C b c) : Composable_Chain C a c :=
  match ch1 with
    | Single f => Chain f ch2
    | Chain f ch' => Chain f (Chain_Compose ch' ch2)
  end.

(**
It doesn't matter if we first chain-compose two composable chains and then get
the compostion of the resutlting chain or if we first compose individual chains
and then composte the two resulting arrows.
*)
Theorem Compose_of_Chain_Compose (C : Category) (a b c : C)
        (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c)
  : ((Compose_of ch2) ∘ (Compose_of ch1))%morphism =
    Compose_of (Chain_Compose ch1 ch2).
Proof.
  induction ch1; auto.
  simpl.
  rewrite <- assoc.
  rewrite IHch1; trivial.
Qed.

(**
If a property holds for all arrows of two chains, then the same property holds
for all arrows in their chain-composition.
*)
Theorem Forall_Links_Chain_Compose (C : Category) (a b c : C)
        (ch1 : Composable_Chain C a b) (ch2 : Composable_Chain C b c)
        (P : ∀ (x y : Obj), (x –≻ y) → Prop) :
  Forall_Links ch1 P → Forall_Links ch2 P → Forall_Links (Chain_Compose ch1 ch2) P.
Proof.
  intros H1 H2.
  induction ch1.
  simpl in *; auto.
  destruct H1 as [H11 H12].
  simpl in *; split; auto.
Qed.
