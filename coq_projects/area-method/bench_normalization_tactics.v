(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Import geometry_tools.
Require Import Rgeometry_tools.

Ltac local_uniformize_signed_areas := Runiformize_signed_areas.
(*
Ltac local_uniformize_signed_areas := uniformize_signed_areas.
*)

Ltac local_basic_simpl := Rbasic_simpl.

Ltac local_uniformize_signed_areas4 := uniformize_signed_areas4.

(* Tests uniformize in the goal *)

Lemma test1 : forall A B C :Point, S A B C = S B C A.
Proof.
intros.
local_uniformize_signed_areas.
auto.
Qed.

Lemma test2 : forall A B C :Point, S A B C + S B A C = 0.
Proof.
intros.
local_uniformize_signed_areas.
ring.
Qed.

Lemma test3 : forall A B C :Point, S A B C + S A C B = 0.
Proof.
intros.
local_uniformize_signed_areas.
ring.
Qed.

Lemma test4 : forall A B C :Point, S A B C +- S B C A = 0.
Proof.
intros.
local_uniformize_signed_areas.
ring.
Qed.

Lemma test5 : forall A B C :Point, S A B C - S C A B = 0.
Proof.
intros.
local_uniformize_signed_areas.
basic_simpl.
ring.
Qed.

Lemma test6 : forall A B C :Point, S A B C + S C B A = 0.
Proof.
intros.
local_uniformize_signed_areas.
ring.
Qed.

(* Test in the hypotheses *)

Lemma test7 : forall A B C :Point, S A B C + S B A C = 0 -> 0=0.
Proof.
intros.
 progress local_uniformize_signed_areas.
ring.
Qed.

Lemma test8 : forall A B C :Point, S A B C + S A C B = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

Lemma test9 : forall A B C :Point, S A B C - S B C A = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

Lemma test10 : forall A B C :Point, S A B C - S C A B = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

Lemma test11 : forall A B C :Point, S A B C + S C B A = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

(* Hypotheses and goal tests *)

Lemma test12 : forall A B C :Point, S A B C - S C A B = 0 -> S A B C + S C B A = 0.
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

Lemma test13 : forall A B C :Point, S A B C + S C B A = 0 ->
S A B C + S B A C = 0 -> S A B C - S B C A = 0 .
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

(*
Lemma test14 : forall A B C : Point, 
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C=0.
Proof.
intros.
local_uniformize_signed_areas.
basic_simpl.
Fring.
Qed.
*)

Lemma test15 : forall A B C : Point,
S A B C = 0 -> S B A C = 0.
Proof.
intros.
progress local_uniformize_signed_areas.
rewrite H.
ring.
Qed.

Lemma test16 : forall A B C : Point,
S A B C + S B A C = S A B C -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
ring.
Qed.

(*
Lemma test17 : forall A B C D E F G H I J K L : Point, 
S A B C + S B A C + S D E F + S E D F +
S G H I + S I G H + S A J K + S K J A +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S J K L + S K L J +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S D E F + S E D F +
S G H I + S I G H + S A J K + S K J A +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S J K L + S K L J +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S D E F + S E D F +
S G H I + S I G H + S A J K + S K J A +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S J K L + S K L J +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S D E F + S E D F +
S G H I + S I G H + S A J K + S K J A +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S A B C + S B B C +
S A B C + S B A C + S J K L + S K L J +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C +
S A B C + S B A C + S A B C + S B A C =0 -> 0=0.
Proof.
intros.
local_uniformize_signed_areas.
auto.

Qed.
*)

Lemma test172 : forall A B C, S A B C <> 0 -> S C B A = 0 -> S B C A =0 -> 0=1.
Proof.
intros.
local_uniformize_signed_areas.
rewrite H1 in H.
intuition.
Qed.

Lemma test173 : forall A B C P, 
 - (S A C P / S B C P * (S B A P / S C A P * (S C B P / S A B P))) = 1 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
auto.
Qed.

Lemma test174 : forall A B C P, 
  S B C P <> 0 ->
  S A B P <> 0 ->
  S C A P <> 0 ->
 False ->
- (S A C P / S B C P * (S B A P / S C A P * (S C B P / S A B P))) = 1.
Proof.
intros.
local_uniformize_signed_areas.
intuition.
Qed.

(* tests S4 *)

Lemma test18 : forall A B C D, S4 A B C D = S4 B C D A.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed.

Lemma test19 : forall A B C D, S4 A B C D = S4 C D A B.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed.

Lemma test20 : forall A B C D, S4 A B C D = S4 D A B C.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed.

Lemma test21 : forall A B C D, S4 A B C D = - S4 A D C B.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test22 : forall A B C D, S4 A B C D = - S4  D C B A.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test23 : forall A B C D, S4 A B C D = - S4 C B A D.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test24 : forall A B C D, S4 A B C D = - S4 B A D C.
Proof.
intros.
local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test25 : forall A B C D, S4 A B C D = - S4 B A D C -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 


Lemma test26 : forall A B C D, S4 A B C D = - S4 B A D C -> S4 A B C D = - S4 B A D C.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test27 : forall A C D, S4 A A C D = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test28 : forall A C D, S4 C D A A = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test29 : forall A C D, S4 A C D A = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test30 : forall A C D, S4 C A A D = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test31 : forall A C D, S4 C A D A = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

Lemma test32 : forall A C D, S4 A C A D = 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas4.
auto.
Qed. 

(* tests uniformize_dirseg *)

Lemma test35 : forall A B, A**B=-B**A.
Proof.
intros.
uniformize_dir_seg.
ring.
Qed.

Lemma test36 : forall A B, A**B=-B**A -> 0=0.
Proof.
intros.
progress uniformize_dir_seg.
auto.
Qed.

(* tests basic_simpl *)

Lemma test40 : forall A C, S A A C + S A C C + S A C A = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test41 : forall A , A**A = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test42 : forall A B, 0*A**B + (1*A**B -1*A**B) = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test43 : forall A B, -A**B + - - A**B + (1*A**B -1*A**B) = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test44 : forall A B, A**B + (-A**B) = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test45 : forall A B, - A**B + (A**B) = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test46 : forall A B, - - A**B + -(A**B) = 0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test47 : forall A B C D, A**B + -(C**D) + (C**D) - (A**B)= 0.
Proof.
intros.
basic_simpl.
ring.
Qed.

Lemma test48 : forall A B C D,  S4 A B A C + A**B + -(C**D) + (C**D) - (A**B)= 0.
Proof.
intros.
basic_simpl.
ring.
Qed.

Lemma test49 : forall A B C D,  S4 A B A C + S A A C + 1* S A B C - - S B A C +  A**B + -(C**D) + (C**D) - (A**B)= 0.
Proof.
intros.
local_uniformize_signed_areas.
basic_simpl.
ring.
Qed.


Lemma test50 : forall A , A<>0 -> A/ A = 1.
Proof.
intros.
basic_field_simpl.
auto.

Qed.

Lemma test51 : forall A , A<>0 -> A/ A = 0 -> 0=1.
Proof.
intros.
basic_field_simpl.
auto.
Qed.


Lemma test52 : forall A B C D,  S4 A B A C + S A A C + 1* S A B C - - S B A C +  A**B + -(C**D) + (C**D) - (A**B)= 0 -> 0=0.
Proof.
intros.
progress local_uniformize_signed_areas.
progress basic_simpl.
auto.
Qed.

Lemma test53 : forall A, A<>0 -> (0+A)/A+(-A)/A=0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test54 : forall x, -x*-x=x*x.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test55 : forall x y, -x*y=-(x*y).
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test56 : forall x y, y<>0 -> (-x)/y=-(x/y).
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test57 : forall y, y<>0 -> 0/y=0.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test58 : forall x y, y<>0 -> (x*y)/y =x.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test59 : forall x y, x<>0 -> (x*y)/x =y.
Proof.
intros.
basic_simpl.
auto.
Qed.

Lemma test60 : forall x y, x<>0 -> (x*y)/x =y -> 0=0.
Proof.
intros.
progress basic_simpl.
auto.
Qed.

Lemma test61 : forall A B C, False -> S A B C=0.
Proof.
intros.
local_uniformize_signed_areas.
intuition.
Qed.

Lemma test62 : forall A B C, False ->  0 = S A B C.
Proof.
intros.
local_uniformize_signed_areas.
intuition.
Qed.


Lemma test65 : forall A B C D E F:Point, S A C D <> 0 ->
S B A F + S A B F = 0.
Proof.
intros.
local_uniformize_signed_areas.
ring.
Qed.


