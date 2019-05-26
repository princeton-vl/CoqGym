(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

Require Import Coq.MSets.MSets.
Require Import CoqMSetInterface.


(* *********************************************************************** *)
(** * Interface *)

Module Type WSfun (X : DecidableType).

  Include CoqMSetInterface.WSetsOn X.

  (** Definition of when two sets are disjoint. *)

  Definition disjoint E F := inter E F [=] empty.

  (** We make [notin] a definition for [~ In x L].  We use this
      definition whenever possible, so that the [intuition] tactic
      does not turn [~ In x L] into [In x L -> False]. *)

  Definition notin x L := ~ In x L.

  (** The predicate [fresh_list L n xs] holds when [xs] is a list of
      length [n] such that the elements are distinct from each other
      and from the elements of [L]. *)

  Fixpoint fresh_list
      (L : t) (n : nat) (xs : list X.t) {struct xs} : Prop :=
    match xs, n with
      | nil, O =>
        True
      | cons x xs', S n' =>
        notin x L /\ fresh_list (union L (singleton x)) n' xs'
      | _, _ =>
        False
    end.

End WSfun.


(* *********************************************************************** *)
(** * Implementation *)

Module Make (X : DecidableType) <: WSfun X.

  Include Coq.MSets.MSetWeakList.Make X.

  Definition disjoint E F := Equal (inter E F) empty.

  Definition notin x L := ~ In x L.

  Fixpoint fresh_list
      (L : t) (n : nat) (xs : list X.t) {struct xs} : Prop :=
    match xs, n with
      | nil, O =>
        True
      | cons x xs', S n' =>
        notin x L /\ fresh_list (union L (singleton x)) n' xs'
      | _, _ =>
        False
    end.

End Make.
