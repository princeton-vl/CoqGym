(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Ensembles.
Require Import Constructive_sets.
Require Import Relations_1.
Require Import Partial_Order.
Require Import Cpo.
Require Import algpodefs.
Require Import Powerset.
Require Import Powerset_facts.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import lpo.
Require Import lpo1.
Require Import alpo.
Require Import newfil.
Section Second_inductive_lemma.
Variable U : Type.
Variable C : Cpo U.

Definition D : PO U := PO_of_cpo U C.

Theorem Triples_are_enough_finite_case :
 (forall x y z : U,
  Consistent U D (Triple U x y z) ->
  ex (fun bsup : U => Lub U D (Triple U x y z) bsup)) ->
 forall X : Ensemble U,
 Finite U X ->
 Included U X (Carrier_of U D) ->
 Consistent U D X -> ex (fun bsup : U => Lub U D X bsup).
Proof.
intro H'; try assumption.
intros X H'0; try assumption.
elim H'0 using Generalized_induction_on_finite_sets.
clear H'0.
clear X.
intros X H'0; elim H'0.
unfold D at 6 in |- *; auto with sets.
clear H'0 X.
intros A H'0; elim H'0.
intros H'1 x H'2 H'3 H'4 H'5; try assumption.
rewrite (Empty_set_zero' U x).
exists x; auto with sets.
clear H'0 A.
intros A H'0; elim H'0.
intros H'1 x H'2 H'3 x0 H'4 H'5 H'6 H'7; try assumption.
2: clear H'0 A.
2: intros A H'0 H'1 x H'2 H'3 x0 H'4 H'5 x1 H'6 H'7 H'8 H'9; try assumption.
clear H'5 H'3 H'1.
rewrite (Empty_set_zero' U x).
unfold Add at 1 in |- *.
rewrite (Couple_as_union U x x0).
rewrite (Triple_as_Couple U x x0).
apply H'.
rewrite <- (Triple_as_union U x x x0).
rewrite (Union_idempotent U (Singleton U x)).
generalize H'7.
rewrite (Empty_set_zero' U x).
unfold Add at 1 in |- *; auto with sets.
clear H'5 H'3 H'1 H'0.
cut
 (forall X : Ensemble U,
  Included U X (Add U (Add U (Add U A x) x0) x1) ->
  Included U X (Carrier_of U D)); auto with sets.
intro L1.
cut
 (forall X : Ensemble U,
  Included U X (Add U (Add U (Add U A x) x0) x1) -> Consistent U D X);
 auto with sets.
2: intros X H'0.
2: apply
    Consistent_downward_stable with (B := Add U (Add U (Add U A x) x0) x1);
    auto with sets.
intro L2.
cut (Included U (Add U A x) (Add U (Add U (Add U A x) x0) x1)); auto with sets.
intro F1.
cut (Included U (Add U A x0) (Add U (Add U (Add U A x) x0) x1));
 auto with sets.
2: apply (Inclusion_is_transitive U) with (Add U (Add U A x) x0);
    auto with sets.
intro F2.
cut (Included U (Add U A x1) (Add U (Add U (Add U A x) x0) x1));
 auto with sets.
intro F3.
cut (Included U (Add U (Add U A x) x0) (Add U (Add U (Add U A x) x0) x1));
 auto with sets.
intro F4.
cut (Included U (Add U (Add U A x) x1) (Add U (Add U (Add U A x) x0) x1));
 auto with sets.
intro F5.
cut (Included U (Add U (Add U A x0) x1) (Add U (Add U (Add U A x) x0) x1));
 auto with sets.
intro F6.
cut
 (Strict_Included U (Add U (Add U A x) x0) (Add U (Add U (Add U A x) x0) x1)).
2: split; auto with sets.
2: red in |- *; simpl in |- *; intro H'0.
2: lapply
    (Extension U (Add U (Add U A x) x0) (Add U (Add U (Add U A x) x0) x1));
    [ intro H'10; elim H'10 | idtac ]; auto with sets.
intro G1.
cut
 (Strict_Included U (Add U (Add U A x) x1) (Add U (Add U (Add U A x) x0) x1)).
2: split; auto with sets.
2: red in |- *; simpl in |- *; intro H'0.
2: lapply
    (Extension U (Add U (Add U A x) x1) (Add U (Add U (Add U A x) x0) x1));
    [ intro H'10; elim H'10 | idtac ]; auto with sets.
2: intros H'1 H'3; try assumption.
2: apply H'4.
2: lapply (incl_add_x U (Add U (Add U A x) x0) (Add U A x) x1);
    [ intro H'14; lapply H'14;
       [ intro H'15; try exact H'15; clear H'14 | clear H'14 ]
    | idtac ]; auto with sets.
intro G2.
cut
 (Strict_Included U (Add U (Add U A x0) x1) (Add U (Add U (Add U A x) x0) x1)).
2: split; auto with sets.
2: red in |- *; simpl in |- *; intro H'0.
2: lapply
    (Extension U (Add U (Add U A x0) x1) (Add U (Add U (Add U A x) x0) x1));
    [ intro H'10; elim H'10 | idtac ]; auto with sets.
2: intros H'1 H'3; try assumption.
2: apply H'2.
2: lapply (incl_add_x U (Add U (Add U A x) x0) (Add U A x0) x1);
    [ intro H'14; lapply H'14;
       [ intro H'15; try exact H'15; clear H'14 | clear H'14 ]
    | idtac ]; auto with sets.
2: lapply (incl_add_x U (Add U A x) A x0);
    [ intro H'14; lapply H'14;
       [ intro H'16; try exact H'16; clear H'14 | clear H'14 ]
    | idtac ]; auto with sets.
intro G3; try assumption.
cut (Strict_Included U (Add U A x0) (Add U (Add U (Add U A x) x0) x1)).
2: apply
    Strict_inclusion_is_transitive_with_inclusion_left
     with (y := Add U (Add U A x0) x1); auto with sets.
intro G4; try assumption.
cut (Strict_Included U (Add U A x1) (Add U (Add U (Add U A x) x0) x1)).
2: apply
    Strict_inclusion_is_transitive_with_inclusion_left
     with (y := Add U (Add U A x) x1); auto with sets.
intro G5; try assumption.
cut (Strict_Included U (Add U A x) (Add U (Add U (Add U A x) x0) x1)).
2: apply
    Strict_inclusion_is_transitive_with_inclusion_left
     with (y := Add U (Add U A x) x0); auto with sets.
intro G6; try assumption.
elim (H'7 (Add U A x));
 [ intros bsup E; try exact E | idtac | idtac | idtac ]; 
 auto with sets.
elim (H'7 (Add U A x0));
 [ intros bsup0 E0; try exact E0 | idtac | idtac | idtac ]; 
 auto with sets.
elim (H'7 (Add U A x1));
 [ intros bsup1 E1; try exact E1 | idtac | idtac | idtac ]; 
 auto with sets.
elim (H'7 (Add U (Add U A x) x0));
 [ intros bsup2 E2; try exact E2 | idtac | idtac | idtac ]; 
 auto with sets.
elim (H'7 (Add U (Add U A x) x1));
 [ intros bsup3 E3; try exact E3 | idtac | idtac | idtac ]; 
 auto with sets.
elim (H'7 (Add U (Add U A x0) x1));
 [ intros bsup4 E4; try exact E4 | idtac | idtac | idtac ]; 
 auto with sets.
elim (H' bsup bsup0 bsup1); [ intros bsup5 E5; try exact E5 | idtac ];
 auto with sets.
exists bsup5; try assumption.
2: apply Consistent_triple_intro.
2: apply
    Compatible_lubs
     with
       (A := Add U A x)
       (B := Add U A x0)
       (C := Add U (Add U A x) x0)
       (c := bsup2); auto with sets.
2: apply
    Compatible_lubs
     with
       (A := Add U A x0)
       (B := Add U A x1)
       (C := Add U (Add U A x0) x1)
       (c := bsup4); auto with sets.
2: apply
    Compatible_lubs
     with
       (A := Add U A x)
       (B := Add U A x1)
       (C := Add U (Add U A x) x1)
       (c := bsup3); auto with sets.
generalize E5.
clear E5.
rewrite (Triple_as_Couple_Singleton U bsup bsup0 bsup1). 
intro E5; try assumption.
unfold Add at 1 in |- *.
cut
 (Union U (Add U (Add U A x) x0) (Singleton U x1) =
  Union U (Add U (Add U A x) x0) (Add U A x1)).
intro H'0; rewrite H'0.
clear H'0.
apply LUaux2 with (a := bsup2) (b := bsup1); auto with sets.
apply LUaux with (A := Couple U bsup bsup0) (B := Singleton U bsup1);
 auto with sets.
3: apply Singleton_has_lub.
clear E5 E4 E3 G6 G5 G4 G3 G2 G1 H'9 H'7 bsup5 bsup4 bsup3 H'6 H'4 H'2 H'.
red in |- *; simpl in |- *.
intros x2 H'; elim H'; auto with sets.
intros x3 H'0; elim H'0; auto with sets.
apply Lub_is_in_Carrier with (X := Add U A x); auto with sets.
apply Lub_is_in_Carrier with (X := Add U A x0); auto with sets.
intros x3 H'0; elim H'0; auto with sets.
apply Lub_is_in_Carrier with (X := Add U A x1); auto with sets.
2: apply Lub_is_in_Carrier with (X := Add U A x1); auto with sets.
apply LUaux with (A := Add U A x) (B := Add U A x0); auto with sets.
cut (Add U (Add U A x) x0 = Union U (Add U A x) (Add U A x0)).
intro H'0; rewrite <- H'0; auto with sets.
cut (Add U (Add U A x) x0 = Union U (Add U A x) (Add U A x0) :>Ensemble U).
clear E5.
(* Rewrite (Triple_as_Couple_Singleton U bsup bsup0 bsup1). *)
intro E5; try assumption.
cut (Lub U D (Couple U bsup bsup0) bsup2).
intro H'1; try assumption.
apply Add_distributes; auto with sets.
apply LUaux with (A := Add U A x) (B := Add U A x0); auto with sets.
rewrite <- (Add_distributes U A A x x0); auto with sets.
cut
 (Union U (Add U (Add U A x) x0) (Singleton U x1) =
  Add U (Add U (Add U A x) x0) x1 :>Ensemble U).
intro H'0; rewrite H'0.
rewrite (Add_distributes U (Add U A x) A x0 x1); auto with sets.
unfold Add at 3 in |- *; auto with sets.
Qed.
Hint Resolve Triples_are_enough_finite_case.

Theorem Triples_are_enough :
 (forall x y z : U,
  Consistent U D (Triple U x y z) ->
  ex (fun bsup : U => Lub U D (Triple U x y z) bsup)) -> 
 Coherent U D.
intro H'; red in |- *; simpl in |- *.
intros X H'0 K; try assumption.
cut (Complete U D).
2: exact (Cpo_cond U C).
unfold D at 1 in |- *.
intro H'3; elim H'3; intros H'6 H'7.
elim (H'7 (Lubs_of_finite_parts U C X));
 [ intros bsup0 E0 | apply LFP_directed ]; auto with sets.
exists bsup0; unfold D at 1 in |- *; auto with sets.
intros Y H'1 H'2; try assumption.
change (ex (fun bsup : U => Lub U D Y bsup)) in |- *.
apply Triples_are_enough_finite_case; auto with sets.
apply Consistent_downward_stable with (B := X); auto with sets.
Qed.
End Second_inductive_lemma.

