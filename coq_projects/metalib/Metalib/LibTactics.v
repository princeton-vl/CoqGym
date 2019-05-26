(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Aaron Bohannon
     Arthur Charg\'eraud *)

(** A library of additional tactics. *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

(** Implementation note: We want [string_scope] to be available for
    the [Case] tactics below, but we want "++" to denote list
    concatenation. *)

Open Scope string_scope.
Open Scope list_scope.


(* *********************************************************************** *)
(** * Variations on built-in tactics *)

(** [unsimpl E] replaces all occurences of [X] in the goal by [E],
    where [X] is the result that tactic [simpl] would give when used
    to reduce [E]. *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.

(** [fold any not] folds all occurrences of [not] in the goal.  It's
    useful for "cleaning up" after the [intuition] tactic. *)

Tactic Notation "fold" "any" "not" :=
  repeat (
    match goal with
    | H: context [?P -> False] |- _ =>
      fold (~ P) in H
    | |- context [?P -> False] =>
      fold (~ P)
    end).

(** The following tactics call [(e)apply] with the first hypothesis
    that succeeds, "first" meaning the hypothesis that comes earliest
    in the context, i.e., higher up in the list. *)

Ltac apply_first_hyp :=
  match reverse goal with
    | H : _ |- _ => apply H
  end.

Ltac eapply_first_hyp :=
  match reverse goal with
    | H : _ |- _ => eapply H
  end.

(** These tactics are the same as above, but are tailored for proofs by
    well-founded induction.  *)

Ltac apply_first_lt_hyp :=
  match reverse goal with
  | H : forall m:nat, m < ?a -> ?b |- _ =>  apply H
  end.

Ltac eapply_first_lt_hyp :=
  match reverse goal with
  | H : forall m:nat, m < ?a -> ?b |- _ =>  eapply H
  end.


(* *********************************************************************** *)
(** * Delineating cases in proofs *)

(** ** Tactic definitions *)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move x at top
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(** ** Example

    One mode of use for the above tactics is to wrap Coq's [induction]
    tactic such that it automatically inserts "case" markers into each
    branch of the proof.  For example:

<<
 Tactic Notation "induction" "nat" ident(n) :=
   induction n; [ Case "O" | Case "S" ].
 Tactic Notation "sub" "induction" "nat" ident(n) :=
   induction n; [ SCase "O" | SCase "S" ].
 Tactic Notation "sub" "sub" "induction" "nat" ident(n) :=
   induction n; [ SSCase "O" | SSCase "S" ].
>>

    Within a proof, one might use the tactics as follows:

<<
    induction nat n.  (* or [induction n] *)
    Case "O".
      ...
    Case "S".
      ...
>>

    If you use such customized versions of the induction tactics, then
    the [Case] tactic will verify that you are working on the case
    that you think you are.  You may also use the [Case] tactic with
    the standard version of [induction], in which case no verification
    is done.

    In general, you may use the [Case] tactics anywhere in a proof you
    wish to leave a "comment marker" in the context. *)


(* *********************************************************************** *)
(** * Tactics for working with lists and proof contexts *)

(** [ltac_map] applies a function [F], with return type [T] and
    exactly one non-implicit argument, to everything in the context
    such that the application type checks.  The tactic returns a list
    containing the results of the applications.

    Implementation note: The check for duplicates in the accumulator
    ([match acc with ...]) is necessary to ensure that the tactic does
    not go into an infinite loop. *)

Ltac ltac_map F :=
  let rec map acc :=
    match goal with
      | H : _ |- _ =>
        let FH := constr:(F H) in
          match acc with
            | context [FH] => fail 1
            | _ => map (List.cons FH acc)
          end
      | _ => acc
    end
  in
  let rec ret T :=
    match T with
      | _ -> ?T' => ret T'
      | ?T' => T'
    end
  in
  let T := ret ltac:(type of F) in
  let res := map (@List.nil T) in
  eval simpl in res.

(** [ltac_map_list tac xs] applies [tac] to each element of [xs],
    where [xs] is a Coq [list]. *)

Ltac ltac_map_list tac xs :=
  match xs with
    | List.nil => idtac
    | List.cons ?x ?xs => tac x; ltac_map_list tac xs
  end.

(** [ltac_remove_dups] takes a [list] and removes duplicate items from
    it.  The supplied list must, after simplification via [simpl], be
    built from only [nil] and [cons].  Duplicates are recognized only
    "up to syntax," i.e., the limitations of Ltac's [context]
    check. *)

Ltac ltac_remove_dups xs :=
  let rec remove xs acc :=
    match xs with
      | List.nil => acc
      | List.cons ?x ?xs =>
        match acc with
          | context [x] => remove xs acc
          | _ => remove xs (List.cons x acc)
        end
    end
  in
  match type of xs with
    | List.list ?A =>
      let xs := eval simpl in xs in
      let xs := remove xs (@List.nil A) in
      eval simpl in (List.rev xs)
  end.
