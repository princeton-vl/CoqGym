(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Ensembles.
Require Import Relations_1.
Require Import Partial_Order.
Require Import Cpo.
Require Import algpodefs.
Require Import Powerset.
Require Import Constructive_sets.
Require Import Finite_sets.
Require Import lpo.
Require Import lpo1.
Section Advanced_lemmas.
Variable U : Type.
Variable D : PO U.
Hint Resolve Lub_definition Upper_Bound_Couple_intro.

Lemma Lub_monotonic :
 forall A B : Ensemble U,
 Included U A B ->
 Included U B (Carrier_of U D) ->
 forall a b : U, Lub U D A a -> Lub U D B b -> Rel_of U D a b.
intros A B H' H'0 a b H'1 H'2; try assumption.
elim H'1; auto with sets.
intros H'3 H'4; apply H'4.
apply Upper_downward_stable with (B := B); auto with sets.
elim H'2; auto with sets.
Qed.

Lemma Compatible_lubs :
 forall A B C : Ensemble U,
 Included U A C ->
 Included U B C ->
 Included U C (Carrier_of U D) ->
 forall a b c : U,
 Lub U D A a -> Lub U D B b -> Lub U D C c -> Compatible U D a b.
intros A B C H' H'0 H'1 a b c H'2 H'3 H'4; red in |- *; simpl in |- *.
intros H'5 H'6; exists c; split.
apply Lub_is_in_Carrier with (X := C); auto with sets.
apply Upper_Bound_Couple_intro; auto with sets.
apply Lub_is_in_Carrier with (X := C); auto with sets.
apply Lub_monotonic with (A := A) (B := C); auto with sets.
apply Lub_monotonic with (A := B) (B := C); auto with sets.
Qed.

Lemma LUaux :
 forall A B : Ensemble U,
 Included U (Union U A B) (Carrier_of U D) ->
 forall a b bsup : U,
 Lub U D A a ->
 Lub U D B b -> Lub U D (Union U A B) bsup -> Lub U D (Couple U a b) bsup.
generalize Rel_of_transitive; intro RoT; red in RoT.
intros A B H' a b bsup H'0 H'1 H'2; try assumption.
elim H'0; elim H'1; elim H'2.
intros H'3 H'4 H'5 H'6 H'7 H'8; try assumption.
elim H'3; elim H'5; elim H'7.
intros H'9 H'10 H'11 H'12 H'13 H'14; try assumption.
apply Lub_definition; auto 8 with sets.
intros y H'15; apply H'4.
apply Upper_Bound_definition; auto with sets.
elim H'15; auto with sets.
elim (Upper_Bound_Couple_inv U D a b y);
 [ intros H'22 H'23; elim H'23; intros H'24 H'25; try exact H'24; clear H'23
 | idtac ]; auto with sets.
intros y0 H'16; elim H'16.
intros x H'17; apply RoT with (y := a); auto with sets.
intros x H'17; apply RoT with (y := b); auto with sets.
Qed.

Lemma LUaux2 :
 forall A B : Ensemble U,
 Included U (Union U A B) (Carrier_of U D) ->
 forall a b bsup : U,
 Lub U D A a ->
 Lub U D B b -> Lub U D (Couple U a b) bsup -> Lub U D (Union U A B) bsup.
generalize Rel_of_transitive; intro RoT; red in RoT.
intros A B H' a b bsup H'0 H'1 H'2; try assumption.
elim H'0; elim H'1; elim H'2.
intros H'3 H'4 H'5 H'6 H'7 H'8; try assumption.
elim H'5; elim H'7.
elim (Upper_Bound_Couple_inv U D a b bsup);
 [ intros H'15 H'16; elim H'16; intros H'17 H'18; try exact H'17; clear H'16
 | idtac ]; auto with sets.
intros H'9 H'10 H'11 H'12; try assumption.
apply Lub_definition; auto with sets.
apply Upper_Bound_definition; auto with sets.
intros y H'13; elim H'13.
intros x H'30; apply RoT with (y := a); auto with sets.
intros x H'30; apply RoT with (y := b); auto with sets.
intros y H'13; try assumption.
apply H'4.
elim H'13; auto 7 with sets.
Qed.

Theorem Lub_of_Union :
 Conditionally_complete U D ->
 forall A B : Ensemble U,
 Included U (Union U A B) (Carrier_of U D) ->
 forall x : U,
 In U (Carrier_of U D) x ->
 Upper_Bound U D (Union U A B) x ->
 forall a b : U,
 Lub U D A a ->
 Lub U D B b ->
 exists bsup : U, Lub U D (Union U A B) bsup /\ Lub U D (Couple U a b) bsup.
intro H'; elim H'.
intros H'0 A B H'1 x H'2 H'3 a b H'4 H'5; try assumption.
elim (H'0 (Union U A B)); [ intros bsup E; try exact E | idtac | idtac ];
 auto with sets.
2: exists x; try assumption.
exists bsup; split; [ try assumption | idtac ].
apply LUaux with (A := A) (B := B); auto with sets.
Qed.

Theorem Lub_of_compacts_is_compact :
 Conditionally_complete U D ->
 forall x y z : U,
 Included U (Couple U x y) (Approximants U D z) ->
 In U (Carrier_of U D) z ->
 exists bsup : U, Lub U D (Couple U x y) bsup /\ Approximant U D z bsup.
Proof.
intros H' x y z H'0 K; red in H'0.
elim (H'0 x); auto with sets.
intros c H'1 H'2.
elim (H'0 y); auto with sets.
intros c' H'3 H'4.
elim H'.
intro H'5; elim (H'5 (Couple U c c')); auto with sets.
2: elim H'1; elim H'3; exists z; auto with sets.
intros bsup H'6; elim H'6.
intros H'7 H'8; exists bsup; split; auto with sets.
apply Defn_of_Approximant; auto with sets.
apply Definition_of_compact.
apply Lub_is_in_Carrier with (X := Couple U c c'); auto with sets.
intros X H'9 H'10.
elim H'1.
intros H'11 H'12; try assumption.
elim H'3.
intros H'13 H'14; try assumption.
clear H'1 H'3.
elim H'10; intros bsup0 h; elim h; clear H'10 h.
intros H'1 H'3; try assumption.
generalize Rel_of_transitive; intro RoT; red in RoT.
elim (H'14 X); auto with sets.
intros x0 H'10; elim H'10; intros H'15 H'17; try exact H'17; clear H'10.
elim (H'12 X); auto with sets.
intros x1 H'10; elim H'10; intros H'18 H'20; try exact H'20; clear H'10.
elim H'9.
intros H'10 H'21 H'22; elim (H'22 x0 x1); auto with sets.
intros y' H'23; elim H'23; intros H'24 H'26; try exact H'24; clear H'23.
exists y'; split; auto with sets.
apply H'8.
elim (Upper_Bound_Couple_inv U D x0 x1 y');
 [ intros H'29 H'30; elim H'30; intros H'31 H'32; clear H'30 | idtac ];
 auto with sets.
apply Upper_Bound_Couple_intro; auto with sets.
apply RoT with (y := x1); auto with sets.
apply RoT with (y := x0); auto with sets.
red in |- *; simpl in |- *.
intros x2 H'23; elim H'23; auto with sets.
exists bsup0; split; auto with sets.
elim (Upper_Bound_Couple_inv U D c c' bsup);
 [ intros H'22 H'23; elim H'23; intros H'24 H'25; clear H'23 | idtac ];
 auto with sets.
apply RoT with (y := bsup); auto with sets.
exists bsup0; split; auto with sets.
elim (Upper_Bound_Couple_inv U D c c' bsup);
 [ intros H'20 H'21; elim H'21; intros H'22 H'23; clear H'21 | idtac ];
 auto with sets.
apply RoT with (y := bsup); auto with sets.
Qed.

Theorem approximants_closed_by_finite_lubs :
 Conditionally_complete U D ->
 forall (x : U) (C : Ensemble U),
 In U (Carrier_of U D) x ->
 Finite U C ->
 Included U C (Approximants U D x) ->
 exists bsup : U, Lub U D C bsup /\ Approximant U D x bsup.
intros H' x C H H'0; elim H'0.
elim (Bottom_is_compact U D);
 [ intros bot E; elim E; intros H'4 H'5; elim H'4; clear E | idtac ];
 auto with sets.
exists bot; split; auto with sets; auto with sets.
apply Lub_definition; auto with sets.
intros y H'1; elim H'1; auto with sets.
intros A H'1 H'2 x0 H'3.
cut (forall x : U, Union U A (Singleton U x) = Add U A x); auto with sets.
intro H'4; rewrite <- (H'4 x0).
clear H'4; intro H'4.
elim H'2; [ intros bsup E; elim E; intros H'6 H'7; clear E H'2 | clear H'2 ];
 auto with sets.
red in H'4.
lapply Lub_of_Union;
 [ intro H'2; lapply (H'2 A (Singleton U x0));
    [ intro H'9; lapply (H'9 x);
       [ intro H'11; lapply H'11;
          [ intro H'12; elim (H'12 bsup x0);
             [ intros bsup0 E; elim E; intros H'17 H'18; try exact H'17;
                clear E H'11
             | clear H'11
             | clear H'11 ]
          | clear H'11 ]
       | idtac ]
    | idtac ]
 | idtac ]; auto with sets.
exists bsup0; split; [ assumption | auto with sets ].
lapply Lub_of_compacts_is_compact;
 [ intro H'5; elim (H'5 bsup x0 x);
    [ intros bsup1 E; elim E; intros H'15 H'16; try exact H'16; clear E
    | idtac
    | idtac ]
 | idtac ]; auto with sets.
lapply (Lub_is_unique U D);
 [ intro H'11; rewrite (H'11 (Couple U bsup x0) bsup0 bsup1) | idtac ];
 auto with sets.
red in |- *; simpl in |- *.
intros x1 H'8; elim H'8; auto with sets.
elim H'7; auto with sets.
apply Singleton_has_lub.
lapply (H'4 x0); [ intro H'8; elim H'8 | idtac ]; auto with sets.
apply Upper_Bound_definition; auto with sets.
intros y H'5; try assumption.
lapply (H'4 y); [ intro H'10; elim H'10 | idtac ]; auto with sets.
red in |- *; simpl in |- *.
intros x1 H'5; try assumption.
lapply (H'4 x1); [ intro H'9; elim H'9 | idtac ]; auto with sets.
Qed.

Theorem Approximants_directed_set :
 Conditionally_complete U D ->
 forall x : U, In U (Carrier_of U D) x -> Directed U D (Approximants U D x).
Proof.
intros H' x H'0; constructor 1; auto with sets.
red in |- *; simpl in |- *; intros x0 H'1; elim H'1; auto with sets.
elim (Bottom_is_compact U D); auto with sets.
intros bot H'1; elim H'1; intros H'2 H'3; clear H'1.
apply Inhabited_intro with (x := bot); auto with sets.
apply Defn_of_Approximants; auto with sets.
elim H'2; auto with sets.
intros x1 x2 H'1; red in H'1; auto with sets.
generalize (H'1 x1); intro h; lapply h;
 [ intro H'2; clear h | clear h; try assumption ]; 
 auto 20 with sets.
generalize (H'1 x2); intro h; lapply h;
 [ intro H'3; clear h | clear h; try assumption ]; 
 auto 20 with sets.
elim H'3.
intros c H'4 H'5.
elim H'2.
intros c' H'6 H'7.
cut (Compatible U D c' c).
intro H'8; try assumption.
lapply Lub_of_compacts_is_compact; [ intro H'9; elim (H'9 c' c x) | idtac ];
 auto with sets.
intros x0 H'10; elim H'10; intros H'11 H'12; elim H'11; clear H'10.
intros H'10 H'13; exists x0; split; auto with sets.
elim H'12; auto with sets.
red in |- *; simpl in |- *.
intros x0 H'10; elim H'10; auto with sets.
red in |- *; simpl in |- *.
intros H'8 H'9; exists x; auto with sets.
Qed.

Theorem Inclusion_of_Approximants :
 Domain U D ->
 forall x y : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) y ->
 Included U (Approximants U D x) (Approximants U D y) -> Rel_of U D x y.
Proof.
intros H' x y H'0 H'1 H'2; try assumption; auto with sets.
red in H'; elim H'; intros H'3 H'4; clear H'; red in H'4.
elim H'4; intros H' H'5; clear H'4; red in H'; auto with sets.
generalize (H' x); intro h; elim h; intros H'4 H'6; clear h; elim H'6;
 auto with sets.
clear H'6; intros H'7 H'8; apply H'8.
generalize (H' y); intro h; elim h; intros H'6 H'9; clear h; try exact H'9;
 auto with sets.
apply Upper_downward_stable with (Approximants U D y); auto with sets.
red in |- *; (intros x0 H'10; elim H'10); auto with sets.
red in |- *; (intros x0 H'10; elim H'10); auto with sets.
apply Upper_Bound_definition; auto with sets.
intros y0 H'10; elim H'10; auto with sets.
Qed.
Hint Resolve Inclusion_of_Approximants.

Theorem Less_imp_Inclusion_of_Approximants :
 Domain U D ->
 forall x y : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) y ->
 Rel_of U D x y -> Included U (Approximants U D x) (Approximants U D y).
Proof.
intros H' x y H'0 H'1 H'2; red in |- *; simpl in |- *.
intros x0 H'3; elim H'3.
generalize Rel_of_transitive; intro RoT; red in RoT.
intros c H'4 H'5; try assumption.
apply Defn_of_Approximants; auto with sets.
apply RoT with (y := x); auto with sets.
Qed.

Theorem Approximants_define_element :
 Domain U D ->
 forall x y : U,
 In U (Carrier_of U D) x ->
 In U (Carrier_of U D) y -> Approximants U D x = Approximants U D y -> x = y.
intros H' x y H'0 H'1 H'2; try assumption.
cut (Same_set U (Approximants U D x) (Approximants U D y)).
intro H'3; elim H'3.
generalize (Rel_of_antisymmetric U D); auto with sets.
rewrite H'2; auto with sets.
Qed.
Hint Resolve Approximants_define_element.
Require Import Classical_sets.
Hint Unfold not.

Theorem Corollary1_1 :
 Domain U D ->
 forall x y : U,
 Compact U D x ->
 In U (Carrier_of U D) y ->
 Strict_Rel_of U D x y ->
 exists z : U, In U (Approximants U D y) z /\ Strict_Rel_of U D x z.
Proof.
unfold Strict_Rel_of in |- *.
intros H' x y H'0 H'1 H'2; elim H'2; intros H'3 H'4; try exact H'3; clear H'2.
lapply Less_imp_Inclusion_of_Approximants;
 [ intro H'2; lapply (H'2 x y);
    [ intro H'7; lapply H'7;
       [ intro H'8; lapply H'8;
          [ intro H'9; try exact H'9; clear H'8 H'7 | clear H'8 H'7 ]
       | clear H'7 ]
    | idtac ]
 | idtac ]; auto with sets.
elim
 (Strict_super_set_contains_new_element U (Approximants U D x)
    (Approximants U D y)); auto 8 with sets.
intros x0 H'5; elim H'5; clear H'5.
intro H'5; elim H'5; clear H'5.
intros c H'5 H'6 H'7; try assumption.
lapply Lub_of_compacts_is_compact; [ intro H'8; elim (H'8 x c y) | idtac ];
 auto with sets.
intros x1 H'11; elim H'11; intros H'12 H'13; elim H'12; clear H'11.
intros H'11 H'14; exists x1.
split; [ idtac | split; [ try assumption | idtac ] ]; auto with sets.
elim H'13; auto with sets.
elim H'11; auto with sets.
red in |- *; simpl in |- *; intro H'15; try exact H'15.
apply H'7.
rewrite H'15; auto with sets.
elim (Upper_Bound_Couple_inv U D x c x1);
 [ intros H'21 H'22; elim H'22; intros H'23 H'24; try exact H'23; clear H'22
 | idtac ]; auto with sets.
red in |- *; simpl in |- *.
intros x1 H'11; elim H'11; auto with sets.
apply Coherent_implies_Conditionally_Complete.
elim H'; auto with sets.
Qed.

Theorem Corollary1_2 :
 Domain U D ->
 forall x : U,
 In U (Carrier_of U D) x ->
 ~ Compact U D x -> ~ Finite U (Approximants U D x).
intros H' x H'0 H'1; red in |- *; simpl in |- *; intro H'2; try exact H'2.
apply H'1.
lapply approximants_closed_by_finite_lubs;
 [ intro H'3; elim (H'3 x (Approximants U D x)) | idtac ]; 
 auto with sets.
intros x0 H'4; elim H'4; intros H'5 H'6; try exact H'5; clear H'4.
elim H'.
intros H'4 H'7; elim H'7.
intro H'9; red in H'9.
elim (H'9 x); intros H'11 H'12; try exact H'12.
intro H'10; clear H'10.
lapply (Lub_is_unique U D);
 [ intro H'14; rewrite (H'14 (Approximants U D x) x x0) | idtac ];
 auto with sets.
elim H'6; auto with sets.
elim H'; auto with sets.
Qed.
End Advanced_lemmas.
Hint Resolve Inclusion_of_Approximants.
Hint Resolve Upper_Bound_Couple_intro.
