(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                  Fil.v                                   *)
(****************************************************************************)

Require Import Ensembles.
Require Import Relations_1.
Require Import podefs.
Require Import podefs_1.
Require Import ps.
Require Import Partial_order_facts.

Section First_inductive_lemmas.
   Variable U : Type.
   Variable B : Ensemble U.
   Variable D : PO U.
   
   Theorem Pairs_are_enough_finite_case :
    Cpo U D ->
    (forall x y : U,
     Compatible U D x y -> exists bsup : U, Lub U D (Couple U x y) bsup) ->
    forall X : Ensemble U,
    Finite U X ->
    Included U X (Carrier_of U D) ->
    (exists maj : U, Upper_Bound U D X maj) ->
    exists bsup : U, Lub U D X bsup.
   intros H' H'0 X H'1; elim H'1; auto.
   intros A H'2 H'3 x H'4 H'5 h; elim h; intros maj E; clear h.
   generalize (Upper_downward_stable U D A (Union U (Singleton U x) A) maj);
    intro h; lapply h;
    [ intro H'6; lapply H'6;
       [ intro H'7; lapply H'7;
          [ intro H'8; lapply H'8;
             [ intro H'9; clear h H'6 H'7 H'8
             | clear h H'6 H'7; try assumption ]
          | clear h H'6 ]
       | clear h ]
    | clear h ]; auto 10.
   lapply H'3;
    [ intro H'6; lapply H'6;
       [ intro H'7; clear H'3 H'6 | exists maj; clear H'3; try assumption ]
    | idtac ]; auto 10.
   elim H'7; intros bsup E0; clear H'7; try exact E0; auto 10.
   generalize (H'0 x bsup); intro h; lapply h;
    [ intro h0; elim h0; intros bsup0 E1; clear h h0; try exact E1
    | clear h ]; clear H'0.
   exists bsup0; apply Lub_definition; auto 10.
   elim E1; intros H'3 H'6.
   elim H'3; intros H'7 H'8.
   apply Upper_Bound_definition; auto 10.
   intros y H'10; elim H'10.
   intros x0 H'11; elim H'11; auto 10.
   intros x0 H'11; auto 10.
   generalize Rel_of_transitive; intro RoT; red in RoT.
   apply RoT with bsup; auto.
   elim E0.
   intro H'12; elim H'12; auto.
   elim E1.
   intros H'3 H'6 y H'7.
   apply H'6.
   elim H'7; intros H'8 H'10.
   apply Upper_Bound_definition; auto.
   intros y0 H'11; elim H'11; auto 10.
   elim H'7.
   elim E0; auto 10.
   red in |- *.
   elim H'9.
   intros H'0 H'3; exists maj; intros H'6 H'7; split;
    [ idtac | apply Upper_Bound_definition ]; auto 10.
   intros y H'10; elim H'10; auto 10.
   elim E; auto 10.
   elim E0; auto 10.
   Qed.
  
   Theorem Pairs_are_enough :
    Cpo U D ->
    (forall x y : U,
     Compatible U D x y -> exists bsup : U, Lub U D (Couple U x y) bsup) ->
    Conditionally_complete U D.
   intros H' H'0; apply Definition_of_Conditionally_complete.
   intros X H'1 H'2.
   generalize (Empty_set_has_lub U D); intro h; lapply h;
    [ intro H'3; clear h | clear h; try assumption ].
   elim H'3; intros bsup E; clear H'3.
   generalize (Inclusion_is_transitive U); intro T; red in T.
   lapply Pairs_are_enough_finite_case;
    [ intro H'3; lapply H'3; [ intro H'4; clear H'3 | try assumption ]
    | idtac ]; auto.
   elim H'; intros H'6 H'7; clear H'.
   generalize
    (H'7
       (fun bsup : U =>
        exists Y : Ensemble U, Included U Y X /\ Finite U Y /\ Lub U D Y bsup));
    intro h; lapply h; [ intro H'; clear h | clear h; try assumption ].
   2: apply Definition_of_Directed; auto 10.
   2: red in |- *; auto 10.
   2: intros x H'; elim H'; auto 10.
   2: intros x0 h; elim h; intros H'3 h0; elim h0; intros H'5 H'8; clear h h0;
       elim H'8; auto 10.
   2: intro H'9; elim H'9; auto 10.
   2: apply Non_empty_intro with bsup.
   2: red in |- *; auto 10.
   2: exists (Empty_set U); split;
       [ idtac | split; [ try assumption | idtac ] ]; 
       auto 10.
   2: intros x1 x2 H'; red in H'; auto 10.
   2: unfold In at 1 in |- *.
   2: unfold In at 2 in H'.
   2: generalize (H' x1); intro h; lapply h;
       [ intro H'3; clear h | clear h; try assumption ]; 
       auto 10.
   2: elim H'3; intros Y h; elim h; intros H'5 h0; elim h0; intros H'8 H'9;
       clear H'3 h h0; try exact H'8.
   2: generalize (H' x2); intro h; lapply h;
       [ intro H'3; clear h | clear h; try assumption ]; 
       auto 10.
   2: elim H'3; intros Y0 h; elim h; intros H'10 h0; elim h0;
       intros H'11 H'12; clear H'3 h h0; try exact H'11.
   2: generalize (Union_of_finite_is_finite U Y Y0); intro h; lapply h;
       [ intro H'3; lapply H'3;
          [ intro H'13; clear h H'3 | clear h; try assumption ]
       | clear h ]; auto 10.
   2: elim H'2; intros maj E0; clear H'2; try exact E0.
   2: generalize (H'4 (Union U Y Y0)); intro h; lapply h;
       [ intro H'2; lapply H'2;
          [ intro H'3; lapply H'3;
             [ intro H'14; clear h H'2 H'3
             | exists maj; clear h H'2; try assumption ]
          | clear h ]
       | clear h ]; auto.
   3: apply Upper_downward_stable with X; auto.
   2: elim H'14; intros bsup0 E1; clear H'14; try exact E1.
   2: exists bsup0; split;
       [ exists (Union U Y Y0); split;
          [ idtac | split; [ try assumption | idtac ] ]
       | idtac ]; auto 10.
   2: elim E1; intros H'2 H'3; clear E1.
   2: generalize (Upper_downward_stable U D Y (Union U Y Y0) bsup0); intro h;
       lapply h;
       [ intro H'14; lapply H'14;
          [ intro H'15; lapply H'15;
             [ intro H'16; lapply H'16;
                [ intro H'17; clear h H'14 H'15 H'16
                | clear h H'14 H'15; try assumption ]
             | clear h H'14 ]
          | clear h ]
       | clear h ]; auto.
   2: generalize (Upper_downward_stable U D Y0 (Union U Y Y0) bsup0); intro h;
       lapply h;
       [ intro H'14; lapply H'14;
          [ intro H'15; lapply H'15;
             [ intro H'16; lapply H'16;
                [ intro H'18; clear h H'14 H'15 H'16
                | clear h H'14 H'15; try assumption ]
             | clear h H'14 ]
          | clear h ]
       | clear h ]; auto.
   2: elim H'12; intros H'14 H'15; clear H'12.
   2: generalize (H'15 bsup0); intro h; lapply h;
       [ intro H'16; clear h | clear h; try assumption ]; 
       auto 10.
   2: elim H'9; intros H'12 H'19; clear H'9.
   2: generalize (H'19 bsup0); intro h; lapply h;
       [ intro H'9; clear h | clear h; try assumption ]; 
       auto 10.
   2: apply Upper_Bound_definition; auto 10.
   2: elim H'2; auto 10.
   2: intros y H'20; elim H'20; auto 10.
   elim H'; intros bsup0 E0; clear H'; try exact E0; auto 10.
   exists bsup0; apply Lub_definition.
   apply Upper_Bound_definition; auto 10.
   generalize
    (Lub_is_in_Carrier U D bsup0
       (fun bsup : U =>
        exists Y : Ensemble U, Included U Y X /\ Finite U Y /\ Lub U D Y bsup));
    intro h; lapply h;
    [ intro H'; lapply H';
       [ intro H'3; clear h H' | clear h; try assumption ]
    | clear h ]; auto 10.
   red in |- *.
   intros x H'; red in H'; auto 10.
   elim H'; intros Y h; elim h; intros H'3 h0; elim h0; intros H'5 H'8;
    clear H' h h0; try exact H'8; auto 10.
   apply Lub_is_in_Carrier with Y; auto.
   elim E0; intros H'3 H'5; clear E0.
   elim H'3; intros H'8 H'9; clear H'3.
   intros y H'; apply H'9; auto 10.
   red in |- *;
    (exists (Singleton U y); split;
      [ idtac | split; [ try assumption | idtac ] ]); 
    auto 10.
   red in |- *; (intros x H'3; elim H'3); auto 10.
   intros y H'; try assumption.
   elim E0; intros H'3 H'5; clear E0; apply H'5.
   apply Upper_Bound_definition; auto 10.
   elim H'; auto 10.
   intros y0 H'8; red in H'8; auto 10.
   elim H'8; intros Y h; elim h; intros H'9 h0; elim h0; intros H'10 H'11;
    clear H'8 h h0; try exact H'11; auto 10.
   elim H'11; intros H'8 H'12; clear H'11.
   apply H'12; auto 10.
   apply Upper_downward_stable with X; auto.
   Qed.
   
End First_inductive_lemmas.