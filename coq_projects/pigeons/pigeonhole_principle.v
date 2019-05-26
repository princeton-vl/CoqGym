(**
  This module presents a proof of the pigeon hole principle, which
  states that if you place n things into m containers, and n >
  m, then one or more of the containers have more than one thing
  in it.

  Our proof proceeds by contradiction. We first show that
  if we have a collection of containers, cs, where every container
  is either empty or has a single item in it, then the number of
  items contained in all of the containers is less than or equal
  to the number of containers. 

  Then we show that if, the number of items contained within a
  collection of containers is greater than the number of containers,
  and every container is either empty or has a single item in it,
  we have a contradiction. Accordingly, we cannot place n items
  into m collections without placing more than one item in a single
  container.

  Copyright (C) 2018 Larry D. Lee Jr. <llee454@gmail.com>

  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU Lesser General Public License as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public
  License along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

Require Import base.
Require Import List.
Require Import Lt.          (* for le_not_lt *)
Require Import Compare_dec. (* for le_dec *)
Require Import PeanoNat.    (* for Nat.nle_succ_0 *)

Module Pigeonhole_Principle.

(** * I. Basic Concepts *) 

(** Represents things (such as pigeons). *)
Parameter thing : Set.

(** Represents containers (such as cubbies). *)
Definition container := list thing.

(** Represents some collection of containers. *)
Definition containers := list container.

(** Counts the number of things in a container. *)
Definition container_num_things := length (A := thing).

(** Counts the number of containers. *)
Definition num_containers := length (A := container).

(** Counts the number of things in some containers. *)
Definition num_things (cs : containers) : nat
  := fold_right (fun c n => container_num_things c + n) 0 cs.

(**
  Accepts a container and asserts that it is either
  empty or has only one item in it.
*)
Definition container_ok (c : container) : Prop
  := container_num_things c <= 1.

(**
  This lemma proves that the OK predicate is
  decideable.

  Note: we will need this when proving that
  [~ Forall container_ok] implies
  [Exists ~ container_ok].
*)
Definition container_ok_dec 
  :  forall (c : container), {container_ok c}+{~ container_ok c}
  := fun c => le_dec (container_num_things c) 1.

(**
  Accepts a set of containers and asserts that
  all of the containers are either empty or only
  contain a single item.
*)
Definition containers_ok (cs : containers) : Prop
  := Forall container_ok cs.

(** * II. Fundamental Proof *)

(**
  This theorem proves that given a collection
  of containers, where every container is either
  empty or has one item in it, then the number
  of items contained in all of the containers
  must be less than or equal to the number
  of containers.
*)
Theorem num_things_num_containers
  :  forall cs : containers,
     containers_ok cs ->
     num_things cs <= num_containers cs.
Proof
  let T cs := containers_ok cs -> num_things cs <= num_containers cs in
  list_ind T
    (* I. case where there are no containers. *)
    (fun _ => le_0_n 0)
    (* II. case where there is more than one container. *)
    (list_ind
      (fun xs => forall cs, T cs -> T (xs :: cs))
      (* II.A. case where the first container is empty. *)
      (fun cs
        (H  : T cs)
        (H0 : containers_ok (nil :: cs))
        => let H1
             :  num_things cs <= num_containers cs
             := H (Forall_tail nil cs H0) in
           (le_S
             (0 + num_things cs)
             (num_containers cs)
             (H1 || a <= num_containers cs @a by plus_O_n (num_things cs))))
      (* II.B. case where the first container has one or more things in it. *)
      (fun x0
        => list_ind
             (fun xs => _ -> forall cs, T cs -> T ((x0 :: xs) :: cs))
             (* II.B.1. case where the first container has only one thing in it. *)
             (fun _ cs
               (H  : T cs)
               (H0 : containers_ok ((x0 :: nil) :: cs))
               => let H1
                    :  num_things cs <= num_containers cs
                    := H (Forall_tail (x0 :: nil) cs H0) in
                  le_n_S (num_things cs) (num_containers cs) H1
                  || a <= S (num_containers cs) @a by Nat.add_1_l (num_things cs))
             (* II.B.2. case where the first container has two or more things in it. *)
             (fun x1 xs _ _ cs
               (H  : T cs)
               (H0 : containers_ok ((x0 :: x1 :: xs) :: cs))
               => False_ind
                    (num_things ((x0 :: x1 :: xs) :: cs) <= num_containers ((x0 :: x1 :: xs) :: cs))
                    ((Nat.nle_succ_0 (length xs))
                      (le_S_n (S (length xs)) 0 ((Forall_inv H0) : S (S (length xs)) <= 1)))))).

(** * III. The Pigeonhole Principle *)

(**
  This lemma proves that if we have a collection
  of containers and the number of things in the
  containers is greater than the number of the
  containers then not all of the containers can
  be empty or have only one thing in it.
*)
Lemma lemma_0
  : forall cs : containers,
    num_things cs > num_containers cs ->
    ~ containers_ok cs.
Proof fun cs
       (H  : num_containers cs < num_things cs)
       (H0 : containers_ok cs)
       => le_not_lt
            (num_things cs)
            (num_containers cs)
            (num_things_num_containers cs H0)
            H.

(**
  This lemma proves that if we have a collection
  of containers and the number of things in the
  containers is greater than the number of
  containers, then one of the containers cannot
  be empty or have only one item in it.
*)
Lemma lemma_1
  :  forall cs : containers,
     num_things cs > num_containers cs ->
     Exists (fun c : container => ~ container_ok c) cs.
Proof fun cs H
       => neg_Forall_Exists_neg container_ok_dec (lemma_0 cs H).

(**
  This theorem proves that if we are given a
  collection of containers and the number of
  things in those containers is greater than the
  number of containers, then one or more of the
  containers has more than one thing in it.
*)
Theorem pigeonhole_principle
  :  forall cs : containers,
     num_things cs > num_containers cs ->
     Exists (fun c : container => container_num_things c > 1) cs.
Proof fun cs H
       => Exists_impl
            (fun c (H0 : ~ container_ok c)
              => not_le (container_num_things c) 1 H0)
            cs
            (lemma_1 cs H).

End Pigeonhole_Principle.
