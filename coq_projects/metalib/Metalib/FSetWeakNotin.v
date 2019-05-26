(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

(** Lemmas and tactics for working with and solving goals related to
    non-membership in finite sets.  The main tactic of interest here
    is [solve_notin].

    Implicit arguments are declared by default in this library. *)

Require Import Coq.FSets.FSetInterface.

Require Import Metalib.CoqFSetDecide.


(* *********************************************************************** *)
(** * Implementation *)

Module Notin_fun
  (E : DecidableType) (Import X : FSetInterface.WSfun E).

Module Import D := CoqFSetDecide.WDecide_fun E X.


(* *********************************************************************** *)
(** * Facts about set non-membership *)

Section Lemmas.

Variables x y  : elt.
Variable  s s' : X.t.

Lemma notin_empty_1 :
  ~ In x empty.
Proof. fsetdec. Qed.

Lemma notin_add_1 :
  ~ In y (add x s) ->
  ~ E.eq x y.
Proof. fsetdec. Qed.

Lemma notin_add_1' :
  ~ In y (add x s) ->
  x <> y.
Proof. fsetdec. Qed.

Lemma notin_add_2 :
  ~ In y (add x s) ->
  ~ In y s.
Proof. fsetdec. Qed.

Lemma notin_add_3 :
  ~ E.eq x y ->
  ~ In y s ->
  ~ In y (add x s).
Proof. fsetdec. Qed.

Lemma notin_singleton_1 :
  ~ In y (singleton x) ->
  ~ E.eq x y.
Proof. fsetdec. Qed.

Lemma notin_singleton_1' :
  ~ In y (singleton x) ->
  x <> y.
Proof. fsetdec. Qed.

Lemma notin_singleton_2 :
  ~ E.eq x y ->
  ~ In y (singleton x).
Proof. fsetdec. Qed.

Lemma notin_remove_1 :
  ~ In y (remove x s) ->
  E.eq x y \/ ~ In y s.
Proof. fsetdec. Qed.

Lemma notin_remove_2 :
  ~ In y s ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_remove_3 :
  E.eq x y ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_remove_3' :
  x = y ->
  ~ In y (remove x s).
Proof. fsetdec. Qed.

Lemma notin_union_1 :
  ~ In x (union s s') ->
  ~ In x s.
Proof. fsetdec. Qed.

Lemma notin_union_2 :
  ~ In x (union s s') ->
  ~ In x s'.
Proof. fsetdec. Qed.

Lemma notin_union_3 :
  ~ In x s ->
  ~ In x s' ->
  ~ In x (union s s').
Proof. fsetdec. Qed.

Lemma notin_inter_1 :
  ~ In x (inter s s') ->
  ~ In x s \/ ~ In x s'.
Proof. fsetdec. Qed.

Lemma notin_inter_2 :
  ~ In x s ->
  ~ In x (inter s s').
Proof. fsetdec. Qed.

Lemma notin_inter_3 :
  ~ In x s' ->
  ~ In x (inter s s').
Proof. fsetdec. Qed.

Lemma notin_diff_1 :
  ~ In x (diff s s') ->
  ~ In x s \/ In x s'.
Proof. fsetdec. Qed.

Lemma notin_diff_2 :
  ~ In x s ->
  ~ In x (diff s s').
Proof. fsetdec. Qed.

Lemma notin_diff_3 :
  In x s' ->
  ~ In x (diff s s').
Proof. fsetdec. Qed.

End Lemmas.


(* *********************************************************************** *)
(** * Hints *)

Hint Resolve
  @notin_empty_1 @notin_add_3 @notin_singleton_2 @notin_remove_2
  @notin_remove_3 @notin_remove_3' @notin_union_3 @notin_inter_2
  @notin_inter_3 @notin_diff_2 @notin_diff_3.


(* *********************************************************************** *)
(** * Tactics for non-membership *)

(** [destruct_notin] decomposes all hypotheses of the form [~ In x s]. *)

Ltac destruct_notin :=
  match goal with
    | H : In ?x ?s -> False |- _ =>
      change (~ In x s) in H;
      destruct_notin
    | |- In ?x ?s -> False =>
      change (~ In x s);
      destruct_notin
    | H : ~ In _ empty |- _ =>
      clear H;
      destruct_notin
    | H : ~ In ?y (add ?x ?s) |- _ =>
      let J1 := fresh "NotInTac" in
      let J2 := fresh "NotInTac" in
      pose proof H as J1;
      pose proof H as J2;
      apply notin_add_1 in H;
      apply notin_add_1' in J1;
      apply notin_add_2 in J2;
      destruct_notin
    | H : ~ In ?y (singleton ?x) |- _ =>
      let J := fresh "NotInTac" in
      pose proof H as J;
      apply notin_singleton_1 in H;
      apply notin_singleton_1' in J;
      destruct_notin
    | H : ~ In ?y (remove ?x ?s) |- _ =>
      let J := fresh "NotInTac" in
      apply notin_remove_1 in H;
      destruct H as [J | J];
      destruct_notin
    | H : ~ In ?x (union ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      pose proof H as J;
      apply notin_union_1 in H;
      apply notin_union_2 in J;
      destruct_notin
    | H : ~ In ?x (inter ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      apply notin_inter_1 in H;
      destruct H as [J | J];
      destruct_notin
    | H : ~ In ?x (diff ?s ?s') |- _ =>
      let J := fresh "NotInTac" in
      apply notin_diff_1 in H;
      destruct H as [J | J];
      destruct_notin
    | _ =>
      idtac
  end.

(** [solve_notin] decomposes hypotheses of the form [~ In x s] and
    then tries some simple heuristics for solving the resulting
    goals. *)

Ltac solve_notin :=
  intros;
  destruct_notin;
  repeat first [ apply notin_union_3
               | apply notin_add_3
               | apply notin_singleton_2
               | apply notin_empty_1
               ];
  auto;
  try tauto;
  fail "Not solvable by [solve_notin]; try [destruct_notin]".


(* *********************************************************************** *)
(** * Examples and test cases *)

(** These examples and test cases are not meant to be exhaustive. *)

Lemma test_solve_notin_1 : forall x E F G,
  ~ In x (union E F) ->
  ~ In x G ->
  ~ In x (union E G).
Proof. solve_notin. Qed.

Lemma test_solve_notin_2 : forall x y E F G,
  ~ In x (union E (union (singleton y) F)) ->
  ~ In x G ->
  ~ In x (singleton y) /\ ~ In y (singleton x).
Proof. split. solve_notin. solve_notin. Qed.

Lemma test_solve_notin_3 : forall x y,
  ~ E.eq x y ->
  ~ In x (singleton y) /\ ~ In y (singleton x).
Proof. split. solve_notin. solve_notin. Qed.

Lemma test_solve_notin_4 : forall x y E F G,
  ~ In x (union E (union (singleton x) F)) ->
  ~ In y G.
Proof. solve_notin. Qed.

Lemma test_solve_notin_5 : forall x y E F,
  ~ In x (union E (union (singleton y) F)) ->
  ~ In y E ->
  ~ E.eq y x /\ ~ E.eq x y.
Proof. split. solve_notin. solve_notin. Qed.

Lemma test_solve_notin_6 : forall x y E,
  ~ In x (add y E) ->
  ~ E.eq x y /\ ~ In x E.
Proof. split. solve_notin. solve_notin. Qed.

Lemma test_solve_notin_7 : forall x,
  ~ In x (singleton x) ->
  False.
Proof. solve_notin. Qed.

End Notin_fun.
