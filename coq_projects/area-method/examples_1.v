(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require  Import area_method.

(** Transitivity of the parallel predicate expressed constructively *)

Theorem parallel_transitivity :
 forall A B C D E F : Point,
 A <> B ->
 on_parallel C D A B ->
 on_parallel E F C D ->
 parallel A B E F.
Proof.
area_method.
Qed.

(** Pseudo-transitivity of the parallel predicate expressed constructively *)

Theorem parallel_pseudo_transitivity :
 forall A B C D E F : Point,
 A <> B ->
 on_parallel C D A B ->
 on_parallel E F A B ->
 parallel C D E F.
Proof.
area_method.
Qed.

(** If AB and CD are two parallel and congruent segments then
AC is parallel to BD *)

Theorem parallellogram_second_parallel :
 forall A B C D : Point,
 on_parallel_d D C A B 1 ->
 parallel A C B D.
Proof.
area_method.
Qed.

(** The construction of a parallelogram using the fact that the diagonals intersect
in the midpoint *)

Theorem parallellogram_construction :
 forall A B C D I : Point,
 is_midpoint I A C ->
 on_line_d D I B (-(1)) ->
 parallel C D A B.
Proof.
area_method.
Qed.

(** An example where a complex sequence of constructions is compiled 
into higher level constructions to ease the elimination process *)

Lemma example_construction_simplification: 
forall A B C D E F G Line_3_b Line_6_b, 
 on_line C A B -> 
 on_parallel Line_3_b C A D -> 
 inter_ll E C Line_3_b B D -> 
 on_parallel Line_6_b C F A ->
 inter_ll G C Line_6_b F B  -> 
 parallel E G D F.
Proof.
area_method.
Qed.

Theorem parallellogram_construction_2 :
 forall A B C D I : Point,
 is_midpoint I A C ->
 on_line_d D I B (-(1)) ->
 parallel C D A B /\ parallel A D B C.
Proof.
area_method.
Qed.

(** We show that the diagonals of a parallelogram intersect in the midpoint *)

Theorem parallelogram_midpoint : 
  forall A B C D I : Point,
  on_parallel_d D C A B (0-1) ->
  inter_ll  I A C B D ->
  A<>C ->
  A<>I -> 
  parallel A I A C ->
  A ** I / A**C = 1 / 2.
Proof.
am_before_field.
intuition.
Ffield.
Qed.

Theorem Prop51Hartsshornebis :
  forall A B C D E : Point,
  ~ Col D A C ->
  ~ Col A B C ->
  is_midpoint D A B ->
  is_midpoint E A C ->
  parallel D E B C -> 
  B <> C -> 
  D ** E / B ** C = 1 / 2.
Proof.
area_method.
Qed.




