(**
  This module defines functions and notations shared by all of the
  modules in this package.

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

(**
  The following notations are introduced here
  to simplify sequences of algebraic rewrites
  which would otherwise be expressed as long
  sequences of eq_ind*.
*)

Require Import List.

Notation "A || B @ X 'by' E"
  := (eq_ind_r (fun X => B) A E) (at level 40, left associativity).

Notation "A || B @ X 'by' <- H"
  := (eq_ind_r (fun X => B) A (eq_sym H)) (at level 40, left associativity).

(**
  The following notation can be used to define
  equality assertions. These are like unittests
  in that they check that a given expression
  reduces to a given value.
*)
Notation "A =:= B"
  := (eq_refl A : A = B) (at level 90).

(** * II. Auxiliary Theorems *)

(**
  Accepts a predicate, [P], and a list, [x0 ::
  xs], and proves that if [P] is true for every
  element in [x0 :: xs], then [P] is true for
  every element in [xs].
*)
Theorem Forall_tail
  :  forall (A : Type) (P : A -> Prop) (x0 : A) (xs : list A), Forall P (x0 :: xs) -> Forall P xs.
Proof fun _ P x0 xs H
       => let H0
            :  forall x, In x (x0 :: xs) -> P x
            := proj1 (Forall_forall P (x0 :: xs)) H in
          let H1
            :  forall x, In x xs -> P x
            := fun x H2
                 => H0 x (or_intror (x0 = x) H2) in
          proj2 (Forall_forall P xs) H1.

Arguments Forall_tail {A} {P} x0 xs.

(**
  Accepts two predicates, [P] and [Q], and a
  list, [xs], and proves that, if [P -> Q],
  and there exists an element in [xs] for which
  [P] is true, then there exists an element in
  [xs] for which [Q] is true.
*)
Theorem Exists_impl
  :  forall (A : Type) (P Q : A -> Prop),
     (forall x : A, P x -> Q x) ->
     forall xs : list A,
       Exists P xs ->
       Exists Q xs.
Proof fun _ P Q H xs H0
       => let H1
            :  exists x, In x xs /\ P x
            := proj1 (Exists_exists P xs) H0 in
          let H2
            :  exists x, In x xs /\ Q x
            := ex_ind
                 (fun x H2
                   => ex_intro
                        (fun x => In x xs /\ Q x)
                        x
                        (conj
                          (proj1 H2)
                          (H x (proj2 H2))))
                 H1 in
          (proj2 (Exists_exists Q xs)) H2.

Arguments Exists_impl {A} {P} {Q} H xs H0.
