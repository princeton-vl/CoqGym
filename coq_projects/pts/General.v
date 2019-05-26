

Require Export Bool.
Require Export Arith.
Require Export Compare_dec.
Require Export Peano_dec.
Require Export MyList.
Require Export MyRelations.

Set Implicit Arguments.
Unset Strict Implicit.

  Definition max_nat (n m : nat) :=
    match le_gt_dec n m with
    | left _ => m
    | right _ => n
    end.

  Lemma least_upper_bound_max_nat :
   forall n m p : nat, n <= p -> m <= p -> max_nat n m <= p.
intros.
unfold max_nat in |- *.
elim (le_gt_dec n m); auto with arith.
Qed.





Require Export Relation_Definitions.

  Definition decide (P : Prop) := {P} + {~ P}.

  Hint Unfold decide: core.



  Inductive Acc3 (A B C : Set) (R : relation (A * (B * C))) :
  A -> B -> C -> Prop :=
      Acc3_intro :
        forall (x : A) (x0 : B) (x1 : C),
        (forall (y : A) (y0 : B) (y1 : C),
         R (y, (y0, y1)) (x, (x0, x1)) -> Acc3 R y y0 y1) -> 
        Acc3 R x x0 x1.


  Lemma Acc3_rec :
   forall (A B C : Set) (R : relation (A * (B * C))) (P : A -> B -> C -> Set),
   (forall (x : A) (x0 : B) (x1 : C),
    (forall (y : A) (y0 : B) (y1 : C),
     R (y, (y0, y1)) (x, (x0, x1)) -> P y y0 y1) -> 
    P x x0 x1) ->
   forall (x : A) (x0 : B) (x1 : C), Acc3 R x x0 x1 -> P x x0 x1.
Proof.
do 6 intro.
fix F 4.
intros.
apply H; intros.
apply F.
generalize H1.
case H0; intros.
apply H2.
exact H3.
Qed.

  Lemma Acc_Acc3 :
   forall (A B C : Set) (R : relation (A * (B * C))) (x : A) (y : B) (z : C),
   Acc R (x, (y, z)) -> Acc3 R x y z. 
Proof.
intros.
change
  ((fun p : A * (B * C) =>
    match p with
    | (x2, (x3, x4)) => Acc3 R x2 x3 x4
    end) (x, (y, z))) in |- *.
elim H.
simple destruct x0.
simple destruct p; intros.
apply Acc3_intro; intros.
apply (H1 (y0, (y1, y2))); auto.
Qed.


Section Principal.

  Variables (A : Set) (P : A -> Prop) (R : A -> A -> Prop).

  Record ppal (x : A) : Prop := Pp_intro
    {pp_ok : P x; pp_least : forall y : A, P y -> R x y}.

  Definition ppal_dec : Set := {x : A | ppal x} + {(forall x : A, ~ P x)}.

End Principal.

