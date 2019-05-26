(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                   ps.v                                   *)
(****************************************************************************)

Require Import Classical.

Require Import Ensembles.
Require Import Relations_1.
Require Import Relations_1_facts.
Require Import podefs.
Require Import podefs_1.

Section The_power_set_partial_order.
   Variable U : Type.
   
   Inductive Power_set (A : Ensemble U) : Ensemble (Ensemble U) :=
       Definition_of_Power_set :
         forall X : Ensemble U,
         Included U X A -> In (Ensemble U) (Power_set A) X.
   Hint Resolve Definition_of_Power_set.
   
   (* Consider a set A, and its powerset P  *)
   Variable A : Ensemble U.
   
   Theorem Empty_set_minimal :
    forall X : Ensemble U, Included U (Empty_set U) X.
   Proof.
   red in |- *; intros X x H'; elim H'.
   Qed.
   Hint Resolve Empty_set_minimal.
   
   Theorem Power_set_non_empty :
    forall A : Ensemble U, Non_empty (Ensemble U) (Power_set A).
   Proof.
   intro A'; apply Non_empty_intro with (Empty_set U); auto.
   Qed.
   Hint Resolve Power_set_non_empty.
   
   Theorem Inclusion_is_an_order : Order (Ensemble U) (Included U).
   Proof.
   auto 8.
   Qed.
   Hint Resolve Inclusion_is_an_order.
   
   Theorem Inclusion_is_transitive : Transitive (Ensemble U) (Included U).
   elim Inclusion_is_an_order; auto.
   Qed.
   Hint Resolve Inclusion_is_transitive.
   
   Theorem Same_set_equivalence : Equivalence (Ensemble U) (Same_set U).
   Proof.
   generalize (Equiv_from_order (Ensemble U) (Included U)); intro H'; elim H';
    auto.
   Qed.

   Theorem Same_set_reflexive : Reflexive (Ensemble U) (Same_set U).
   Proof.
   elim Same_set_equivalence; auto.
   Qed.
   Hint Resolve Same_set_reflexive.
   
   Theorem Power_set_PO : PO (Ensemble U).
   Proof.
   apply Definition_of_PO with (Power_set A) (Included U); auto.
   Defined.
   
   Theorem Union_minimal :
    forall a b X : Ensemble U,
    Included U a X -> Included U b X -> Included U (Union U a b) X.
   Proof.
   intros a b X H' H'0; red in |- *; (intros x H'1; elim H'1); auto.
   Qed.
   Hint Resolve Union_minimal.
   
   Theorem Intersection_maximal :
    forall a b X : Ensemble U,
    Included U X a -> Included U X b -> Included U X (Intersection U a b).
   Proof.
   auto.
   Qed.
   
   Theorem Union_increases_l :
    forall a b : Ensemble U, Included U a (Union U a b).
   Proof.
   auto.
   Qed.
   
   Theorem Union_increases_r :
    forall a b : Ensemble U, Included U b (Union U a b).
   Proof.
   auto.
   Qed.
   
   Theorem Intersection_decreases_l :
    forall a b : Ensemble U, Included U (Intersection U a b) a.
   Proof.
   intros a b; red in |- *; auto.
   intros x H'; elim H'; auto.
   Qed.
   
   Theorem Intersection_decreases_r :
    forall a b : Ensemble U, Included U (Intersection U a b) b.
   Proof.
   intros a b; red in |- *; auto.
   intros x H'; elim H'; auto.
   Qed.
   Hint Resolve Union_increases_l Union_increases_r Intersection_decreases_l
     Intersection_decreases_r.
   
   Theorem Empty_set_is_Bottom :
    Bottom (Ensemble U) Power_set_PO (Empty_set U).
   Proof.
   apply Bottom_definition; simpl in |- *; auto.
   Qed.
   Hint Resolve Empty_set_is_Bottom.
  
   Theorem Union_is_Lub :
    forall a b : Ensemble U,
    Included U a A ->
    Included U b A ->
    Lub (Ensemble U) Power_set_PO (Couple (Ensemble U) a b) (Union U a b).
   Proof.
   intros a b H' H'0.
   apply Lub_definition; simpl in |- *.
   apply Upper_Bound_definition; simpl in |- *.
   auto.
   intros y H'1; elim H'1; auto.
   intros y H'1; elim H'1; simpl in |- *; auto.
   Qed.


   Theorem Intersection_is_Glb :
    forall a b : Ensemble U,
    Included U a A ->
    Included U b A ->
    Glb (Ensemble U) Power_set_PO (Couple (Ensemble U) a b)
      (Intersection U a b).
   Proof.
   intros a b H' H'0.
   apply Glb_definition.
   apply Lower_Bound_definition; simpl in |- *.
   apply Definition_of_Power_set; auto.
   generalize Inclusion_is_transitive; intro IT; red in IT; apply IT with a;
    auto.
   intros y H'1; elim H'1; auto.
   intros y H'1; elim H'1; simpl in |- *; auto.
   Qed.
   
   Theorem Empty_set_zero :
    forall X : Ensemble U, Union U (Empty_set U) X = X.
   Proof.
   auto 10.
   Qed.
   
   Theorem Union_commutative :
    forall A B : Ensemble U, Union U A B = Union U B A.
   Proof.
   auto.
   Qed.
   
   Theorem Union_associative :
    forall A B C : Ensemble U,
    Union U (Union U A B) C = Union U A (Union U B C).
   Proof.
   auto 20.
   Qed.
   
   Theorem Non_disjoint_union :
    forall (X : Ensemble U) (x : U),
    In U X x -> Union U (Singleton U x) X = X.
   Proof.
   intros X x H'; try assumption; auto 10.
   apply Extensionality_Ensembles; unfold Same_set in |- *; split;
    auto.
   red in |- *; auto 10.
   intros x0 H'0; elim H'0; auto 10.
   intros x1 H'1; elim H'1; auto 10.
   Qed.
   
   Theorem Finite_plus_one_is_finite :
    forall (X : Ensemble U) (x : U),
    Finite U X -> Finite U (Union U (Singleton U x) X).
   Proof.
   intros X x H'.
   generalize (classic (In U X x)); intro h; elim h;
    [ intro H'0; clear h; try exact H'0 | clear h; intro H'0 ];
    auto 10.
   generalize (Non_disjoint_union X x); intro h; lapply h;
    [ intro H'1; rewrite H'1; clear h | clear h ]; 
    auto.
   Qed.
   Hint Resolve Finite_plus_one_is_finite.
  
   Theorem Singleton_is_finite : forall x : U, Finite U (Singleton U x).
   Proof.
   intro x; generalize (Empty_set_zero (Singleton U x)); intro h;
    rewrite <- h; clear h.
   generalize (Union_commutative (Empty_set U) (Singleton U x)); intro h;
    rewrite h; clear h; auto.
   Qed.
   Hint Resolve Singleton_is_finite.
   
   Theorem Union_of_finite_is_finite :
    forall X Y : Ensemble U,
    Finite U X -> Finite U Y -> Finite U (Union U X Y).
   Proof.
   intros X Y H'; elim H'.
   generalize (Empty_set_zero Y); intro h; rewrite h; clear h; auto.
   clear A.
   intros AA H'0 H'1 x H'2 H'3.
   generalize (Union_associative (Singleton U x) AA Y); intro h; rewrite h;
    clear h; auto.
   Qed.
   
End The_power_set_partial_order.
Hint Resolve Empty_set_minimal.
Hint Resolve Power_set_non_empty.
Hint Resolve Inclusion_is_an_order.
Hint Resolve Inclusion_is_transitive.
Hint Resolve Same_set_reflexive.
Hint Resolve Union_minimal.
Hint Resolve Same_set_reflexive.
Hint Resolve Union_increases_l.
Hint Resolve Union_increases_r.
Hint Resolve Intersection_decreases_l.
Hint Resolve Intersection_decreases_r.
Hint Resolve Empty_set_is_Bottom.
Hint Resolve Empty_set_zero.
Hint Resolve Finite_plus_one_is_finite.
Hint Resolve Singleton_is_finite.

