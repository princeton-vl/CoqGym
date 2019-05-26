(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export geometry_tools_lemmas.
Require Export my_field_tac.

(***********************************************)
(* Unification tactic for signed areas         *)
(***********************************************)
(* Simplification is necessary for termination *)
(***********************************************)

Ltac uniformize_signed_areas_goal :=
  repeat
   match goal with
   |  |- context [(- - ?X1)] =>
       replace (- - X1) with X1 by apply simplring1
   |  |- context [(S ?X1 ?X1 ?X2)] =>
       replace (S X1 X1 X2) with 0 by apply trivial_col1
   |  |- context [(S ?X2 ?X1 ?X1)] =>
       replace (S X2 X1 X1) with 0 by apply trivial_col2
   |  |- context [(S ?X1 ?X2 ?X1)] =>
       replace (S X1 X2 X1) with 0 by apply trivial_col3
   |  |- context [(S ?X1 ?X2 ?X3)] =>
    ( let Truc := fresh in
    match goal with
       |  |- context [(S ?X4 ?X5 ?X6)] =>
            (assert (Truc : S X4 X5 X6 = - S X1 X2 X3);
             [ apply S_3 || apply S_2 || apply S_4
             | rewrite Truc; clear Truc ]) ||
             (assert (Truc : S X4 X5 X6 = S X1 X2 X3);
               [ apply S_0 || apply S_1 | rewrite Truc; clear Truc ])
       end)
   end.

Ltac generalize_all_areas :=
   repeat match goal with
          H: context [(S ?X1 ?X2 ?X3)] |- _=> revert H
 end.

Ltac uniformize_signed_areas :=
  generalize_all_areas;uniformize_signed_areas_goal;intros.


Lemma S4Simpl_1 : forall A B C : Point, S4 A B B C = S A B C.
intros.
unfold S4 in |- *.
uniformize_signed_areas.
ring.
Qed.

Lemma S4Simpl_2 : forall A B C : Point, S4 A B C C = S A B C.
intros.
unfold S4 in |- *.
uniformize_signed_areas.
ring.
Qed.

Lemma S4Simpl_3 : forall A B C : Point, S4 A A B C = S A B C.
intros.
unfold S4 in |- *.
uniformize_signed_areas.
ring.
Qed.

Lemma S4Simpl_4 : forall A B C : Point, S4 A B C A = S A B C.
intros.
unfold S4 in |- *.
uniformize_signed_areas.
ring.
Qed.


Lemma S4Simpl_5 : forall A C D : Point, S4 C A D A = 0.
Proof.
intros.
unfold S4 in |- *.
uniformize_signed_areas.
ring.
Qed.

Lemma S4Simpl_6 : forall A C D : Point, S4 A C A D = 0.
Proof.
intros.
unfold S4 in |- *.
uniformize_signed_areas.
ring.
Qed.

Lemma half : 1- 1/2 = 1/2.
Proof.
field.
auto with Geom.
Qed.

Ltac uniformize_signed_areas4_goal :=
  repeat
   match goal with
   |  |- context [(- - ?X1)] =>      
       replace (- - X1) with X1; [ idtac | apply simplring1 ]
   |  |- context [(S4 ?X1 ?X2 ?X1 ?X3)] =>
	rewrite (S4Simpl_6 X1 X2 X3)
   |  |- context [(S4 ?X2 ?X1 ?X3 ?X1)] =>
        rewrite (S4Simpl_5 X1 X2 X3)
   |  |- context [(S4 ?X1 ?X2 ?X2 ?X3)] =>
        rewrite (S4Simpl_1 X1 X2 X3)
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X3)] =>
        rewrite (S4Simpl_2 X1 X2 X3)
   |  |- context [(S4 ?X1 ?X1 ?X2 ?X3)] =>
        rewrite (S4Simpl_3 X1 X2 X3)
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X1)] =>
        rewrite (S4Simpl_4 X1 X2 X3)
   |  |- context [(S4 ?X1 ?X2 ?X3 ?X4)] =>
       match goal with
       |  |- context [(S4 ?X5 ?X6 ?X7 ?X8)] =>
           (assert (Truc : S4 X5 X6 X7 X8 = - S4 X1 X2 X3 X4);
             [ apply S4_5 || apply S4_6 || apply S4_7 || apply S4_8
             | rewrite Truc; clear Truc ]) ||
             (assert (Truc : S4 X5 X6 X7 X8 = S4 X1 X2 X3 X4);
               [ apply S4_2 || apply S4_3 || apply S4_4
               | rewrite Truc; clear Truc ])
       end
   end.

Ltac generalize_all_areas4 :=
   repeat match goal with
          H: context [(S4 ?X1 ?X2 ?X3 ?X4)] |- _=> revert H
 end.

Ltac uniformize_signed_areas4 :=
  generalize_all_areas4;uniformize_signed_areas4_goal;intros.




(****************************************)
(* Signed distance unification tactic   *)
(****************************************)

Ltac uniformize_dir_seg_goal :=
  repeat
   match goal with
   |  |- context [(- - ?X1)] =>
       replace (- - X1) with X1; [ idtac | apply simplring1 ]
   |  |- context [(?X1 ** ?X1)] =>
       rewrite <- (nuldirseg X1)
   |  |- context [(?X1 ** ?X2)] =>
       match goal with
       |  |- context [(?X3 ** ?X4)] =>
           match constr:((X3, X4)) with
           | (?X2, ?X1) => rewrite (A1a X1 X2)
           end
       end
   end.

Ltac generalize_all_seg :=
   repeat match goal with
          H: context [(?X1 ** ?X2)] |- _=> revert H
 end.

Ltac uniformize_dir_seg_general :=
  generalize_all_seg;uniformize_dir_seg_goal;intros.

Ltac try_rw A B := try rewrite <- (A1a B A) in *;
                   try rewrite    (A1a A B) in *.

Ltac uniformize_dir_seg_spec := match reverse goal with

 | [A : Point, B : Point, C : Point, 
    D : Point, E : Point, F : Point,
    G : Point |- _ ] => fail 1

 | [A : Point, B : Point, C : Point, D: Point, E: Point, F: Point |- _ ] => 
     try_rw A B; try_rw A C; try_rw A D; try_rw A E; try_rw A F; 
     try_rw B C; try_rw B D; try_rw B E; try_rw B F;
     try_rw C D; try_rw C E; try_rw C F;
     try_rw D E; try_rw D F;
     try_rw E F

 | [A : Point, B : Point, C : Point, D: Point, E: Point |- _ ] => 
     try_rw A B; try_rw A C; try_rw A D; try_rw A E; 
     try_rw B C; try_rw B D; try_rw B E;
     try_rw C D; try_rw C E;
     try_rw D E

 | [A : Point, B : Point, C : Point, D: Point |- _ ] => 
     try_rw A B; try_rw A C; try_rw A D; try_rw B C; try_rw B D; try_rw C D

 | [A : Point, B : Point, C : Point |- _ ] => 
     try_rw A B; try_rw A C;try_rw B C

 | [A : Point, B : Point |- _ ] => 
     try_rw A B
end.
 

Ltac uniformize_dir_seg := uniformize_dir_seg_spec || uniformize_dir_seg_general.

Lemma test_uniformize_dir_seg_1 : forall A B,
A ** B = - B**A.
Proof.
intros.
uniformize_dir_seg.
ring.
Qed.

Lemma test_uniformize_dir_seg_2 : forall A B,
A ** B = - B**A ->
A ** B = - B**A.
Proof.
intros.
uniformize_dir_seg.
ring.
Qed.

Lemma test_uniformize_dir_seg_3 : forall A B C,
A ** B = - B**A + A**C + C**A + B**C + C**A ->
A ** B = - B**A.
Proof.
intros.
uniformize_dir_seg.
ring.
Qed.

Lemma test_uniformize_dir_seg_4 : forall A B C D,
A ** B = - B**A + A**C + C**A + B**C + C**A + D**A + A**D->
A ** B = - B**A.
Proof.
intros.
uniformize_dir_seg.
ring.
Qed.

Lemma test_uniformize_dir_seg_5 : forall A B C D, forall  E F G H I : Point,
A ** B = - B**A + A**C + C**A + B**C + C**A + D**A + A**D->
A ** B = - B**A.
Proof.
intros.
uniformize_dir_seg.
ring.
Qed.


(*************************)
(* Simplification tactic *)
(*************************)

Hint Rewrite S4Simpl_1  S4Simpl_2 S4Simpl_3 S4Simpl_4 S4Simpl_5 S4Simpl_6 : S4_simplifications.
Hint Rewrite <- trivial_col1: S_simplifications.
Hint Rewrite <- trivial_col2: S_simplifications.
Hint Rewrite <- trivial_col3: S_simplifications.
Hint Rewrite <- nuldirseg : seg_simplifications.
Hint Rewrite half  : seg_simplifications.

Ltac basic_non_field_simpl:= autorewrite with ring_simplification 
                               S4_simplifications 
                             S_simplifications
          seg_simplifications in *.


Ltac basic_simpl := repeat (progress (basic_non_field_simpl;basic_field_simpl)).


