(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008                                           *)
(***************************************************************************)

Require Export area_elimination_lemmas.

Theorem combine_inter_parallel : forall A B C E F X Y r, 
(on_parallel_d X C A B r) -> 
(inter_ll Y C X E F) ->
~ Col C A B ->
(on_inter_line_parallel Y C E F A B).
Proof.
intro.
unfold on_parallel_d, inter_ll, on_inter_line_parallel.
intros.
DecompAndAll.
repeat split;try assumption.

assert (C<>X).
unfold not;intro.
assert (parallel C X E F).
subst C.
Geometry.
intuition.
cut  (parallel A B C Y).
Geometry.
eapply col_par_par.
apply H.
Geometry.
Geometry.

unfold not;intro.
assert (parallel C X E F).
assert (parallel C X A B).
Geometry.
eapply parallel_transitivity;eauto.
intuition.

Qed.

Ltac put_on_inter_line_parallel :=
  repeat match goal with
  | H:(on_parallel_d  ?X ?C ?A ?B), G:(inter_ll ?Y ?C ?X ?E ?F) |- _ =>
         let T:= fresh in  assert (T:=combine_inter_parallel A B C E F X Y H G);clear H G
end.

(*
Lemma essai1: forall A B C D E F G Line_3_b Line_6_b, 
(on_line C A B) -> 
(on_parallel Line_3_b C A D) -> 
(inter_ll E C Line_3_b B D) -> 
(on_parallel Line_6_b C F A) ->
(inter_ll G C Line_6_b F B) -> (parallel E G D F).
Proof.
intros.
put_on_inter_line_parallel.



Goal forall A B C D E F G, 
(on_line C A B) ->
(on_inter_line_parallel E C B D A D)  -> 
(on_inter_line_parallel G C B F F A)  -> (parallel E G D F).
Proof.
intros.
put_on_inter_line_parallel.
AutoGeom.
Qed.


Goal forall A B C D E F G Line_3_b Line_6_b, 
(on_line C A B) /\ 
(on_parallel Line_3_b C A D) /\ 
(inter_ll E Line_3_b C B D) /\ 
(on_parallel Line_6_b C F A) /\
(inter_ll G F B Line_6_b C) -> (parallel E G D F).
Proof.
Qed.
*)