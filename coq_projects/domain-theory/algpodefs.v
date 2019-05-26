(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Ensembles.
Require Import Relations_1.
Require Import Partial_Order.
Require Import Cpo.
Require Import Image.
Require Import Integers.
Section Algebraic_partial_orders.
Variable U : Type.
Variable D : PO U.

Let D_C := Carrier_of U D.

Let D_R := Rel_of U D.

Definition Consistent (A : Ensemble U) : Prop :=
  Included U A D_C ->
  forall x y : U, Included U (Couple U x y) A -> Compatible U D x y.

Definition Coherent : Prop :=
  forall A : Ensemble U,
  Included U A D_C -> Consistent A -> exists bsup : U, Lub U D A bsup.

Inductive Compact (x : U) : Prop :=
    Definition_of_compact :
      In U D_C x ->
      (forall X : Ensemble U,
       Directed U D X ->
       (exists bsup : U, Lub U D X bsup /\ D_R x bsup) ->
       exists y : U, In U X y /\ D_R x y) -> Compact x.

Inductive Approximant (x c : U) : Prop :=
    Defn_of_Approximant : Compact c -> D_R c x -> Approximant x c.

Inductive Approximants (x : U) : Ensemble U :=
    Defn_of_Approximants :
      forall c : U, Compact c -> D_R c x -> In U (Approximants x) c.

Definition Algebraic : Prop :=
  forall x : U, Directed U D (Approximants x) /\ Lub U D (Approximants x) x.

Definition Denumerable (A : Ensemble U) : Prop :=
  exists f : U -> nat, injective U nat f.

Definition Omega_algebraic : Prop :=
  Algebraic /\ Denumerable (fun x : U => Compact x).

Definition Domain : Prop := Coherent /\ Omega_algebraic.
End Algebraic_partial_orders.
Hint Unfold Consistent Coherent.
Hint Resolve Definition_of_compact.
Hint Resolve Defn_of_Approximant.
Hint Resolve Defn_of_Approximants.
