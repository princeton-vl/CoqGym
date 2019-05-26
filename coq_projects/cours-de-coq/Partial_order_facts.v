(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Initial Version: Frederic Prost, July 1993                          *)
(*      Revised Version: Gilles Kahn, September 1993                        *)
(*                               INRIA Sophia-Antipolis, FRANCE             *)
(*      Revised Version: Jean-Christophe Filliatre, January 1995            *)
(*                               ENS-Lyon, FRANCE                           *)
(*                                                                          *)
(****************************************************************************)
(*                          Partial_order_facts.v                           *)
(****************************************************************************)

Require Import Ensembles.
Require Import Relations_1.
Require Import podefs.
Require Import podefs_1.
Require Import ps.

Section Lemmas_on_partial_orders.
   Variable U : Type.
   Variable B : Ensemble U.
   Variable D : PO U.
   
   Theorem Rel_of_reflexive : forall x : U, Rel_of U D x x.
   elim D; simpl in |- *; auto.
   intros C R H' H'0; elim H'0; auto 10.
   Qed.
   Hint Resolve Rel_of_reflexive.
   
   Theorem Rel_of_antisymmetric : Antisymmetric U (Rel_of U D).
   elim D; simpl in |- *; auto.
   intros C R H' H'0; elim H'0; auto 10.
   Qed.
   Hint Resolve Rel_of_antisymmetric.
   
   Theorem Rel_of_transitive : Transitive U (Rel_of U D).
   elim D; simpl in |- *; auto.
   intros C R H' H'0; elim H'0; auto 10.
   Qed.
   Hint Resolve Rel_of_transitive.
   
   Theorem Couple_included_in_carrier :
    forall x y : U,
    In U (Carrier_of U D) x ->
    In U (Carrier_of U D) y -> Included U (Couple U x y) (Carrier_of U D).
   intros x y H' H'0; red in |- *; auto 20.
   intros x0 H'1; elim H'1; auto 20.
   Qed.
   Hint Resolve Couple_included_in_carrier.
   
   Theorem Lub_is_in_Carrier :
    forall (bsup : U) (X : Ensemble U),
    Included U X (Carrier_of U D) ->
    Lub U D X bsup -> In U (Carrier_of U D) bsup.
   intros bsup X H' H'0; elim H'0; auto 20.
   intro H'1; elim H'1; auto 20.
   Qed.
   
   Theorem Singleton_has_lub :
    forall x : U, In U (Carrier_of U D) x -> Lub U D (Singleton U x) x.
   intros x H'; auto 20.
   apply Lub_definition; auto 10.
   apply Upper_Bound_definition; auto 10.
   intros y H'0; elim H'0; auto 10.
   intros y H'0; elim H'0; auto 10.
   Qed.
   Hint Resolve Singleton_has_lub.
   
   Theorem Empty_set_has_Upper_Bound :
    exists maj : U, Upper_Bound U D (Empty_set U) maj.
   elim D.
   intros C R n o.
   elim n.
   intros x H'; exists x.
   apply Upper_Bound_definition; auto.
   intros y H'0; elim H'0; auto.
   Qed.
   Hint Resolve Empty_set_has_Upper_Bound.
   
   Theorem Empty_set_has_lub :
    Cpo U D -> exists bsup : U, Lub U D (Empty_set U) bsup.
   intro H'; elim H'.
   intro h; elim h; intros bot E; clear h.
   intro H'0; exists bot.
   apply Lub_definition.
   apply Upper_Bound_definition.
   elim E; auto.
   intros y H'1; elim H'1; auto.
   intros y H'1; elim H'1; auto.
   elim E; auto.
   Qed.
   Hint Resolve Empty_set_has_lub.
 
   Theorem Upper_downward_stable :
    forall (A B : Ensemble U) (maj : U),
    Included U A (Carrier_of U D) ->
    Included U B (Carrier_of U D) ->
    Included U A B -> Upper_Bound U D B maj -> Upper_Bound U D A maj.
   clear B.
   intros A BB maj H' H'0 H'1 H'2; elim H'2; auto.
   Qed.
   
   Theorem Conditionally_complete_has_a_bottom :
    Conditionally_complete U D -> exists bot : U, Bottom U D bot.
   intro H'; elim H'; auto 10.
   intro H'0; generalize (H'0 (Empty_set U)); intro h; lapply h;
    [ intro H'1; lapply H'1;
       [ intro h0; elim h0; intros bsup E; clear h H'1 h0; elim E | clear h ]
    | clear h ]; auto 10.
   intros H'1 H'2; exists bsup; apply Bottom_definition; auto 10.
   elim H'1; auto 10.
   intros y H'3; try assumption; auto 10.
   apply H'2; auto 10.
   apply Upper_Bound_definition; auto 10.
   intros y0 H'4; elim H'4; auto 10.
   Qed.
   Hint Resolve Conditionally_complete_has_a_bottom.

   Theorem Compatible_is_reflexive : Reflexive U (Compatible U D).
   red in |- *; intro x; red in |- *.
   exists x; intros H' H'0; split; [ idtac | apply Upper_Bound_definition ];
    auto.
   intros y H'1; elim H'1; auto.
   Qed.
   
   Theorem Couple_is_symmetric :
    forall x y : U, Couple U x y = Couple U y x :>Ensemble U.
   intros x y; apply Extensionality_Ensembles; apply Same_set_intro;
    red in |- *; (intros x0 H'; elim H'); auto 10.
   Qed.
   
   Theorem Compatible_is_symmetric : Symmetric U (Compatible U D).
   red in |- *; unfold Compatible in |- *.
   intros x y h; elim h; intros z E; clear h.
   elim Couple_is_symmetric; exists z; auto.
   Qed.
   
End Lemmas_on_partial_orders.
Hint Resolve Couple_included_in_carrier.
Hint Resolve Singleton_has_lub.
Hint Resolve Empty_set_has_Upper_Bound.
Hint Resolve Empty_set_has_lub.
Hint Resolve Conditionally_complete_has_a_bottom.

