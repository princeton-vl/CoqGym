(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Ensembles.
Require Import Relations_1.
Require Import Partial_Order.
Require Import Cpo.
Require Import algpodefs.
Require Import Powerset.
Section Lemmas_on_partial_orders.
Variable U : Type.
Variable B : Ensemble U.
Variable D : PO U.

Theorem Rel_of_reflexive : forall x : U, Rel_of U D x x.
Proof.
elim D.
intros Carrier_of Rel_of PO_cond1 PO_cond2; elim PO_cond2; auto with sets.
Qed.
Hint Resolve Rel_of_reflexive.

Theorem Rel_of_antisymmetric : Antisymmetric U (Rel_of U D).
Proof.
elim D.
intros Carrier_of Rel_of PO_cond1 PO_cond2; elim PO_cond2; auto with sets.
Qed.
Hint Resolve Rel_of_antisymmetric.

Theorem Rel_of_transitive : Transitive U (Rel_of U D).
Proof.
elim D.
intros Carrier_of Rel_of PO_cond1 PO_cond2; elim PO_cond2; auto with sets.
Qed.
Hint Resolve Rel_of_transitive.

Theorem Couple_included_in_carrier :
 forall x y : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) y -> Included U (Couple U x y) (Carrier_of U D).
Proof.
intros x y H' H'0; red in |- *.
intros x0 H'1; elim H'1; auto with sets.
Qed.
Hint Resolve Couple_included_in_carrier.

Theorem Lub_is_in_Carrier :
 forall (bsup : U) (X : Ensemble U),
 Included U X (Carrier_of U D) ->
 Lub U D X bsup -> In U (Carrier_of U D) bsup.
Proof.
intros bsup X H' H'0; elim H'0.
intro H'1; elim H'1; auto with sets.
Qed.

Theorem Singleton_has_lub :
 forall x : U, In U (Carrier_of U D) x -> Lub U D (Singleton U x) x.
Proof.
intros x H'.
apply Lub_definition.
apply Upper_Bound_definition; auto with sets.
intros y H'0; elim H'0; auto with sets.
intros y H'0; elim H'0; auto with sets.
Qed.
Hint Resolve Singleton_has_lub.

Theorem Empty_set_has_Upper_Bound :
 exists maj : U, Upper_Bound U D (Empty_set U) maj.
Proof.
elim D.
intros C R cond1 cond2.
elim cond1.
intros x H'; exists x.
apply Upper_Bound_definition; auto with sets.
intros y H'0; elim H'0; auto with sets.
Qed.
Hint Resolve Empty_set_has_Upper_Bound.

Theorem Anyone_is_Upper_Bound_of_Empty_set :
 forall x : U, In U (Carrier_of U D) x -> Upper_Bound U D (Empty_set U) x.
intros x H'; apply Upper_Bound_definition; auto with sets.
intros y H'0; elim H'0; auto with sets.
Qed.
Hint Resolve Anyone_is_Upper_Bound_of_Empty_set.

Theorem Empty_set_has_lub :
 forall C : Cpo U, exists bsup : U, Lub U (PO_of_cpo U C) (Empty_set U) bsup.
Proof.
intro C; elim C; simpl in |- *.
intros PO_of_cpo Cpo_cond; elim Cpo_cond; clear Cpo_cond.
intro H'; elim H'; clear H'.
intros bot is_bot H'0; exists bot; simpl in |- *.
elim is_bot; intros H' H'1.
apply Lub_definition.
apply Upper_Bound_definition; auto with sets.
intros y H'2; elim H'2; auto with sets.
intros y H'2; elim H'2; auto with sets.
Qed.
Hint Resolve Empty_set_has_lub.

Theorem Upper_downward_stable :
 forall (A B : Ensemble U) (maj : U),
 Included U A (Carrier_of U D) ->
 Included U B (Carrier_of U D) ->
 Included U A B -> Upper_Bound U D B maj -> Upper_Bound U D A maj.
Proof.
intros A B0 maj H' H'0 H'1 H'2; elim H'2; auto with sets.
Qed.

Theorem Conditionally_complete_has_a_bottom :
 Conditionally_complete U D -> exists bot : U, Bottom U D bot.
Proof.
intro H'; elim H'.
intro H'0; elim (H'0 (Empty_set U));
 [ intros bsup E; elim E | idtac | idtac ]; auto with sets.
intros H'1 H'2; exists bsup.
elim H'1; auto with sets.
Qed.
Hint Resolve Conditionally_complete_has_a_bottom.

Theorem Bottom_is_compact :
 Conditionally_complete U D ->
 exists bot : U, Bottom U D bot /\ Compact U D bot.
Proof.
intro H'; lapply Conditionally_complete_has_a_bottom;
 [ intro H'0 | try assumption ].
elim H'0; intros bot E; clear H'0.
exists bot; split; auto with sets.
apply Definition_of_compact; auto with sets.
elim E; auto with sets.
intros X H'0; elim H'0.
intros H'1 H'2; elim H'2.
intros x H'3 H'4 H'5; try assumption.
exists x; auto with sets.
elim E; auto with sets.
Qed.
Hint Resolve Bottom_is_compact.

Theorem Compact_is_in_Carrier :
 forall x : U, Compact U D x -> In U (Carrier_of U D) x.
Proof.
intros x H'; elim H'; auto with sets.
Qed.
Hint Resolve Compact_is_in_Carrier.

Theorem Compatible_is_reflexive : forall x : U, Compatible U D x x.
Proof.
intro x; red in |- *; simpl in |- *.
intros H'2 H'3; exists x.
split; [ assumption | apply Upper_Bound_definition ]; auto with sets.
intros y H'; elim H'; auto with sets.
Qed.
Hint Resolve Compatible_is_reflexive.

Theorem Couple_is_symmetric :
 forall x y : U, Couple U x y = Couple U y x :>Ensemble U.
Proof.
intros x y; apply Extensionality_Ensembles; red in |- *.
split; red in |- *; (intros x0 H'; elim H'); auto with sets.
Qed.

Theorem Compatible_is_symmetric :
 forall x y : U, Compatible U D x y -> Compatible U D y x.
Proof.
unfold Compatible in |- *.
intros x y H' H'0 H'1.
rewrite <- (Couple_is_symmetric x y); auto with sets.
Qed.
Hint Immediate Compatible_is_symmetric.

Theorem Compatible_imp_consistent :
 forall x y : U, Compatible U D x y -> Consistent U D (Couple U x y).
intros x y H'; red in |- *; simpl in |- *.
intros H'0 x0 y0 H'1; try assumption.
red in H'1.
lapply (H'1 x0); [ intro H'3 | auto with sets ].
lapply (H'1 y0); [ intro H'4 | auto with sets ].
elim H'4.
elim H'3; auto with sets.
elim H'3; auto with sets.
Qed.

Theorem Consistent_imp_compatible :
 forall x y : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) y ->
 Consistent U D (Couple U x y) -> Compatible U D x y.
Proof.
intros x y H' H'0 H'1; red in H'1; simpl in H'1; auto with sets.
Qed.

Theorem Coherent_implies_Conditionally_Complete :
 Coherent U D -> Conditionally_complete U D.
Proof.
intro H'; red in H'.
apply Definition_of_Conditionally_complete.
intros X H'0 H'1.
apply H'; auto with sets.
red in |- *; simpl in |- *.
intros H'2 x y H'3; red in |- *; simpl in |- *.
intros H'4 H'5.
elim H'1; intros maj E; try exact E; clear H'1.
exists maj; elim E; auto with sets.
Qed.
Hint Resolve Coherent_implies_Conditionally_Complete.

Theorem Coherent_has_a_bottom :
 Coherent U D -> exists bot : U, Bottom U D bot.
Proof.
auto with sets.
Qed.
Hint Resolve Coherent_has_a_bottom.

Theorem Coherent_implies_Complete : Coherent U D -> Complete U D.
Proof.
intro H'.
apply Definition_of_Complete; auto with sets.
intros X H'0; apply H'.
elim H'0; auto with sets.
red in |- *; simpl in |- *.
intros H'1 x y H'2; elim H'0.
intros H'3 H'4 H'5; lapply (H'5 x y); [ intro H'8; elim H'8 | auto with sets ].
intros x0 H'6; red in |- *; simpl in |- *.
intros H'7 H'9; exists x0.
intuition.
Qed.
End Lemmas_on_partial_orders.
Hint Resolve Rel_of_reflexive.
Hint Resolve Rel_of_antisymmetric.
Hint Resolve Rel_of_transitive.
Hint Resolve Couple_included_in_carrier.
Hint Resolve Singleton_has_lub.
Hint Resolve Empty_set_has_Upper_Bound.
Hint Resolve Anyone_is_Upper_Bound_of_Empty_set.
Hint Resolve Empty_set_has_lub.
Hint Resolve Conditionally_complete_has_a_bottom.
Hint Resolve Bottom_is_compact.
Hint Resolve Compact_is_in_Carrier.
Hint Resolve Compatible_is_reflexive.
Hint Immediate Compatible_is_symmetric.
Hint Resolve Coherent_implies_Conditionally_Complete.
Hint Resolve Coherent_has_a_bottom.

