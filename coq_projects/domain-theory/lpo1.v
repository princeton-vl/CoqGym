(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Ensembles.
Require Import Relations_1.
Require Import Partial_Order.
Require Import Cpo.
Require Import algpodefs.
Require Import Powerset.
Require Import lpo.
Require Import Constructive_sets.
Require Import Finite_sets.
Section more_lemmas.
Variable U : Type.
Variable B : Ensemble U.
Variable D : PO U.

Theorem Upper_Bound_is_in_Carrier :
 forall (X : Ensemble U) (bound : U),
 Included U X (Carrier_of U D) ->
 Upper_Bound U D X bound -> In U (Carrier_of U D) bound.
intros X bound H' H'0; elim H'0; auto with sets.
Qed.

Theorem Lower_Bound_is_in_Carrier :
 forall (X : Ensemble U) (bound : U),
 Included U X (Carrier_of U D) ->
 Lower_Bound U D X bound -> In U (Carrier_of U D) bound.
intros X bound H' H'0; elim H'0; auto with sets.
Qed.

Theorem Lub_is_unique :
 Conditionally_complete U D ->
 forall (C : Ensemble U) (bsup1 bsup2 : U),
 Lub U D C bsup1 -> Lub U D C bsup2 -> bsup1 = bsup2.
intros H' C bsup1 bsup2 H'0 H'1.
apply (Rel_of_antisymmetric U D); (elim H'1; elim H'0; auto with sets).
Qed.

Theorem Upper_Bound_Couple_intro :
 forall x y z : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) y ->
 In U (Carrier_of U D) z ->
 Rel_of U D x z -> Rel_of U D y z -> Upper_Bound U D (Couple U x y) z.
intros x y z H' H'0 H'1 H'2 H'3.
apply Upper_Bound_definition; auto with sets.
intros y0 H'4; elim H'4; auto with sets.
Qed.
Hint Resolve Upper_Bound_Couple_intro.

Theorem Upper_Bound_Couple_inv :
 forall x y z : U,
 Upper_Bound U D (Couple U x y) z ->
 Rel_of U D x z /\ Rel_of U D y z /\ In U (Carrier_of U D) z.
intros x y z H'; elim H'; auto with sets.
Qed.

Theorem Upper_Bound_Singleton_intro :
 forall x z : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) z -> x = z -> Upper_Bound U D (Singleton U x) z.
intros x z H' H'0 H'1; rewrite <- H'1.
apply Upper_Bound_definition; auto with sets.
intros y H'2; elim H'2; auto with sets.
Qed.
Hint Resolve Upper_Bound_Singleton_intro.

Theorem Upper_Bound_Singleton_inv :
 forall x z : U, Upper_Bound U D (Singleton U x) z -> Rel_of U D x z.
intros x z H'; elim H'; auto with sets.
Qed.
Hint Resolve Upper_Bound_Singleton_inv.

Theorem Non_empty_has_glb :
 Conditionally_complete U D ->
 forall X : Ensemble U,
 Included U X (Carrier_of U D) ->
 Inhabited U X -> exists binf : U, Glb U D X binf.
Proof.
intro H'; elim H'; clear H'.
intros H'0 X H'1 H'2.
generalize (Lower_Bound_is_in_Carrier X); intro L.
elim (H'0 (fun z : U => Lower_Bound U D X z)); auto with sets.
intros bsup H'3; elim H'3; intros H'4 H'6.
exists bsup; auto with sets.
apply Glb_definition; auto with sets.
apply Lower_Bound_definition; auto with sets.
apply Lub_is_in_Carrier with (X := fun z : U => Lower_Bound U D X z);
 auto with sets.
intros y H'7; apply H'6.
apply Upper_Bound_definition; auto with sets.
intros y0 H'8; elim H'8; auto with sets.
intros y H'7; elim H'7; auto with sets.
intros H'8 H'9; elim H'4; auto with sets.
elim H'2; intros x0 H'3; exists x0.
apply Upper_Bound_definition; auto with sets.
intros y H'4; elim H'4; auto with sets.
Qed.

Theorem Bounded_implies_consistent :
 forall X : Ensemble U,
 Included U X (Carrier_of U D) ->
 ex (fun maj : U => Upper_Bound U D X maj) -> Consistent U D X.
intros X H' H'0; elim H'0; intros maj E; try exact E; clear H'0.
red in |- *; simpl in |- *.
intros H'0 x y H'1; red in |- *; simpl in |- *.
intros H'2 H'3; exists maj; split.
elim E; auto with sets.
elim E; auto with sets.
Qed.

Theorem Consistent_downward_stable :
 forall B : Ensemble U,
 Included U B (Carrier_of U D) ->
 Consistent U D B ->
 forall A : Ensemble U, Included U A B -> Consistent U D A.
Proof.
auto 6 with sets.
Qed.

Lemma Consistent_triple_intro :
 forall x y z : U,
 Compatible U D x y ->
 Compatible U D y z -> Compatible U D x z -> Consistent U D (Triple U x y z).
intros x y z H' H'0 H'1; red in |- *; simpl in |- *.
intros H'2 x0 y0 H'3; try assumption.
red in H'3.
lapply (H'3 x0); [ intro H'5 | try assumption ]; auto with sets.
lapply (H'3 y0); [ intro H'6 | idtac ]; auto with sets.
clear H'3.
elim H'6; elim H'5; auto with sets.
Qed.
End more_lemmas.
Hint Resolve Upper_Bound_Couple_intro.
Hint Resolve Upper_Bound_Singleton_intro.
Hint Resolve Upper_Bound_Singleton_inv.
Hint Resolve Bounded_implies_consistent.

