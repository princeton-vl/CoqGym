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
Require Import alpo.
Require Import Finite_sets_facts.
Section First_inductive_lemma.
Variable U : Type.
Variable C : Cpo U.

Let D : PO U := PO_of_cpo U C.

Theorem Pairs_are_enough_finite_case :
 (forall x y : U,
  Compatible U D x y -> ex (fun bsup : U => Lub U D (Couple U x y) bsup)) ->
 forall X : Ensemble U,
 Finite U X ->
 Included U X (Carrier_of U D) ->
 ex (fun maj : U => Upper_Bound U D X maj) ->
 ex (fun bsup : U => Lub U D X bsup).
Proof.
intros H' X H'0; elim H'0; auto with sets.
unfold D at 3 in |- *; auto with sets.
unfold Add in |- *.
intros A H'1 H'2 x H'3 H'4 H'5.
elim H'5; intros maj E; try exact E; clear H'5.
elim H'2; [ intros bsupA E0; elim E0; clear H'2 | clear H'2 | clear H'2 ];
 auto with sets.
2: exists maj;
    apply Upper_downward_stable with (B := Union U A (Singleton U x));
    auto with sets.
intros H'2 H'6.
elim (H' bsupA x); [ intros bsup E1; elim E1 | idtac ]; auto with sets.
2: red in |- *; simpl in |- *.
2: intros H'7 H'8; exists maj; elim E; auto 7 with sets.
intros H'5 H'7; try assumption.
exists bsup; try assumption.
apply LUaux2 with (a := bsupA) (b := x); auto with sets.
Qed.

Inductive Lubs_of_finite_parts (X : Ensemble U) : Ensemble U :=
    Lubs_of_finite_parts_def :
      forall (bsup : U) (Y : Ensemble U),
      Included U Y X ->
      Finite U Y -> Lub U D Y bsup -> In U (Lubs_of_finite_parts X) bsup.

Theorem LFP_directed :
 forall X : Ensemble U,
 (forall Y : Ensemble U,
  Included U Y X -> Finite U Y -> exists bsup : U, Lub U D Y bsup) ->
 Included U X (Carrier_of U D) ->
 Consistent U D X -> Directed U D (Lubs_of_finite_parts X).
intros X K H' L; apply Definition_of_Directed.
red in |- *; simpl in |- *; intros x H'0; elim H'0; auto with sets.
intros bsup Y H'1 H'2 H'3; apply Lub_is_in_Carrier with (X := Y);
 auto with sets.
elim (Empty_set_has_lub U C); intros bsup E.
apply Inhabited_intro with (x := bsup).
apply Lubs_of_finite_parts_def with (Y := Empty_set U); auto with sets.
intros x1 x2 H'4; red in H'4.
lapply (H'4 x1); [ intro H'1; elim H'1 | idtac ]; auto with sets.
intros bsup Y H'0 H'2 H'3; try assumption.
lapply (H'4 x2); [ intro H'6; elim H'6 | idtac ]; auto with sets.
intros bsup0 Y0 H'5 H'7 H'8; try assumption.
lapply (Union_preserves_Finite U Y Y0);
 [ intro H'12; lapply H'12; [ intro H'13; clear H'12 | clear H'12 ] | idtac ];
 auto with sets.
elim (K (Union U Y Y0)); [ intros bsup1 E | idtac | idtac ]; auto with sets.
exists bsup1; split.
apply Lubs_of_finite_parts_def with (Y := Union U Y Y0); auto with sets.
apply Upper_Bound_Couple_intro.
apply Lub_is_in_Carrier with (X := Y); auto with sets.
apply Lub_is_in_Carrier with (X := Y0); auto with sets.
apply Lub_is_in_Carrier with (X := Union U Y Y0); auto with sets.
elim H'3.
intros H'10 H'11; apply H'11.
elim E; intros H'12 H'14;
 apply Upper_downward_stable with (B := Union U Y Y0); 
 auto with sets.
elim H'8.
intros H'10 H'11; apply H'11.
elim E; intros H'12 H'14;
 apply Upper_downward_stable with (B := Union U Y Y0); 
 auto with sets.
Qed.

Theorem Lub_is_LFP :
 forall X : Ensemble U,
 Included U X (Carrier_of U D) ->
 forall bsup : U, Lub U D (Lubs_of_finite_parts X) bsup -> Lub U D X bsup.
intros X K bsup E0; elim E0.
intros H'4 H'5; apply Lub_definition; auto with sets.
apply Upper_Bound_definition; auto with sets.
apply Lub_is_in_Carrier with (X := Lubs_of_finite_parts X); auto with sets.
red in |- *; simpl in |- *; intros x H'8; elim H'8.
intros bsup0 Y H'9 H'10 H'11; apply Lub_is_in_Carrier with Y; auto with sets.
intros y H'8; elim H'4.
intros H'9 H'10; apply H'10.
apply Lubs_of_finite_parts_def with (Y := Singleton U y); auto with sets.
red in |- *; simpl in |- *.
intros x H'11; elim H'11; auto with sets.
apply Singleton_is_finite.
intros y H'8; apply H'5.
apply Upper_Bound_definition.
elim H'8; auto with sets.
intros y0 H'9; elim H'9.
intros bsup1 Y H'10 H'11 H'12; elim H'12.
intros H'13 H'14; apply H'14.
apply Upper_downward_stable with (B := X); auto with sets.
Qed.
Hint Resolve Lub_is_LFP.
Hint Resolve Pairs_are_enough_finite_case.

Theorem Pairs_are_enough :
 (forall x y : U,
  Compatible U D x y -> ex (fun bsup : U => Lub U D (Couple U x y) bsup)) ->
 Conditionally_complete U D.
Proof.
intro H'; apply Definition_of_Conditionally_complete.
intros X H'1 H'2.
cut (Complete U D).
2: exact (Cpo_cond U C).
intro H'3; elim H'3; intros H'6 H'7.
elim (H'7 (Lubs_of_finite_parts X)); [ intros bsup0 E0 | apply LFP_directed ];
 auto with sets.
exists bsup0; auto with sets.
auto with sets.
intros Y H'4 H'5; apply Pairs_are_enough_finite_case; auto with sets.
elim H'2; intros maj E; try exact E; clear H'2.
exists maj.
apply Upper_downward_stable with (B := X); auto with sets.
Qed.
End First_inductive_lemma.
Hint Resolve Lub_is_LFP.

